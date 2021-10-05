-- imports, etc {{{
{-# LANGUAGE
    BlockArguments, DeriveLift, DeriveTraversable, FlexibleInstances,
    LambdaCase, OverloadedLists, OverloadedStrings, QuasiQuotes,
    TemplateHaskell, TupleSections, TypeSynonymInstances
  #-}

import Prelude hiding (lex)
import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import Data.Foldable
import Data.Maybe
import Data.Void

import Data.Function

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Except

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ ((<+>))
import qualified Text.Parsec.String as Pa
import qualified Text.Parsec as Pa
import Text.Parsec ((<?>))

import Language.Haskell.TH.Syntax hiding (Type, lift)
import qualified Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Quote

import Control.Monad.ST
import Data.STRef.Strict
-- }}}

data BaseType = Nat | Bool deriving (Eq, Show, Lift)

data Type' v = B BaseType
             | List (Type' v)
             | Type' v :-> Type' v
             | V v
  deriving (Eq, Show, Functor, Foldable, Traversable, Lift)

type Meta = String

type Type = Type' Meta

type Subst' u v = Map u (Type' v)
type Subst      = Subst' Meta Meta

data Problem' v = Type' v :?: Type' v
  deriving (Eq, Show, Functor, Foldable, Traversable, Lift)
newtype Problems' v = P (Seq (Problem' v)) -- queue of equations
  deriving (Eq, Show, Functor, Foldable, Traversable)
instance Lift v => Lift (Problems' v) where -- {{{
  liftTyped (P p) = [||P (Seq.fromList $$(liftTyped (toList p)))||] -- }}}

type Problem  = Problem'  Meta
type Problems = Problems' Meta

data Error = Occurs Meta Type | Clash Type Type deriving Show

-- quasiquoter {{{
lex :: Pa.Parser a -> Pa.Parser a
lex p = p <* Pa.spaces

tok :: String -> Pa.Parser ()
tok = void . lex . Pa.string

parseType :: Pa.Parser Type
parseType = Pa.chainr1 atom arr where
  arr = (:->) <$ tok "->"
  atom = B Nat  <$  tok "Nat"
     <|> B Bool <$  tok "Bool"
     <|> List   <$> (tok "List" *> atom)
     <|> V      <$> lex meta
     <|> (tok "(" *> parseType <* tok ")" <?> "parenthesised type")
  meta = Pa.char '?' *> Pa.many1 (Pa.satisfy isAlphaNum) <?> "metavariable"

parseProblem :: Pa.Parser Problem
parseProblem = do
  a <- parseType
  _ <- tok "≐" <|> tok "==="
  b <- parseType
  pure $ a :?: b

parseProblems :: Pa.Parser Problems
parseProblems = P . Seq.fromList <$> parseProblem `Pa.sepEndBy` tok ";"

ty, pb :: QuasiQuoter
ty = parsecQQ parseType     [t|Type|]
pb = parsecQQ parseProblems [t|Problems|]

parsecQQ :: Lift a => Pa.Parser a -> Q TH.Type -> QuasiQuoter
parsecQQ p t = QuasiQuoter qexp undefined undefined undefined where
  qexp str = case Pa.parse (Pa.spaces *> p <* Pa.eof) "quote" str of
    Left err -> fail $ show err
    Right x  -> [|x :: $t|]

-- }}}
-- pretty printing {{{
class Pretty a where
  ppPrec :: Int -> a -> PP.Doc

ppr :: Pretty a => a -> PP.Doc
ppr = ppPrec 0

instance Pretty Void where ppPrec _ = absurd
instance Pretty Meta where ppPrec _ = PP.text

instance Pretty BaseType where
  ppPrec _ Nat  = "Nat"
  ppPrec _ Bool = "Bool"

instance Pretty a => Pretty (Type' a) where
  ppPrec _ (B b) = ppr b
  ppPrec d (List t) =
    PP.maybeParens (d > 9) $ PP.hang "List" 2 $ ppPrec 10 t
  ppPrec d (a :-> b) =
    PP.maybeParens (d > 0) $ PP.hang (ppPrec 1 a <+> "->") 2 (ppPrec 0 b)
  ppPrec _ (V x) = "?" <> ppr x

instance (Pretty u, Pretty v) => Pretty (Subst' u v) where
  ppPrec _ =
    PP.braces . PP.sep . PP.punctuate ";" . map ppPair . Map.toList
    where ppPair (x, t) = PP.sep [ppr $ V x, "|->", ppPrec 10 t]

instance Pretty Error where
  ppPrec _ (Occurs i t) =
      PP.hang (PP.sep ["metavariable", ppr (V i), "occurs in"]) 2 (ppr t)
  ppPrec _ (Clash s t) =
      PP.hang "type constructor clash:" 2 $
        PP.sep [ppr s <+> "and", ppr t]

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  ppPrec d = either (ppPrec d) (ppPrec d)

instance Pretty a => Pretty (Problem' a) where
  ppPrec d (a :?: b) = PP.maybeParens (d > 0) $
    PP.hang (ppPrec 9 a <+> "≐") 2 (ppPrec 9 b)

instance Pretty a => Pretty (Problems' a) where
  ppPrec _ (P ps) = PP.braces $ PP.sep $ PP.punctuate ";" $ map ppr $ toList ps
-- }}}

--------------------------------------------------------------------------------

-- apply a substitution, with an action to perform on an unbound variable
subst :: (Ord v) => Subst' v v -> Type' v -> Type' v
subst _ (B b)     = B b
subst σ (List a)  = List $ subst σ a
subst σ (a :-> b) = subst σ a :-> subst σ b
subst σ (V i)     = fromMaybe (V i) $ Map.lookup i σ

-- substitute a new binding in an outstanding problem
substProb :: Meta -> Type -> Problem -> Problem
substProb α b (c :?: d) = sub1 c :?: sub1 d where sub1 = subst [(α, b)]

-- substitute a new binding in the outstanding problems
substProbs :: Meta -> Type -> Problems -> Problems
substProbs α b (P ps) = P $ fmap (substProb α b) ps

occurs :: Eq a => a -> Type' a -> Bool
occurs α = any (== α)

--------------------------------------------------------------------------------
-- pure, 𝒪(n²) version

unify1 :: Type -> Type -> Either Error Subst
unify1 a b = unify $ P [a :?: b]

unify :: Problems -> Either Error Subst
unify = unifyLoop []

unifyLoop :: Subst -> Problems -> Either Error Subst
unifyLoop σ (P Empty)      = pure σ
unifyLoop σ (P (p :<| ps)) = case p of
  -- decompose arrows and lists
  List a    :?: List b    -> unifyLoop σ $ P $ ps :|> a :?: b
  (a :-> b) :?: (c :-> d) -> unifyLoop σ $ P $ ps :|> a :?: c :|> b :?: d

  -- base types must be the same
  B a :?: B b | a == b -> unifyLoop σ $ P ps

  -- see below
  V α :?: b   -> unifyVar α b σ $ P ps
  a   :?: V β -> unifyVar β a σ $ P ps

  -- otherwise, constructor clash e.g. INT ≟ (A :-> B)
  a :?: b -> throwError $ Clash a b

-- skip α ≟ α; otherwise occurs check; otherwise solve variable
unifyVar :: Meta -> Type -> Subst -> Problems -> Either Error Subst
unifyVar α b σ ps
  | b == V α   = unifyLoop σ ps
  | occurs α b = throwError $ Occurs α b
  | otherwise  = unifyLoop (bind α b σ) (substProbs α b ps)

-- add a new binding
bind :: Meta -> Type -> Subst -> Subst
bind α t σ =
  σ & fmap (subst [(α, t)]) -- substitute α in all existing bindings…
    & Map.insert α t         -- …then add one for α itself

--------------------------------------------------------------------------------
-- impure, 𝒪(n) version

type RefVar' s = STRef s (Maybe (RefType s))
data RefVar  s = RV Meta (RefVar' s)
type RefMap  s = STRef s (Map Meta (RefVar' s))
type RefType s = Type' (RefVar s)

type RefSubst    s = Subst' Meta (RefVar s)
type RefProblem  s = Problem'    (RefVar s)
type RefProblems s = Problems'   (RefVar s)

instance Eq (RefVar s) where RV _ ref1 == RV _ ref2 = ref1 == ref2

makeRefVar1 :: RefMap s -> Meta -> ST s (RefVar s) -- {{{
makeRefVar1 refMap var = do
  vars <- readSTRef refMap
  case Map.lookup var vars of
    Just ref -> pure $ RV var ref
    Nothing  -> do
      ref <- newSTRef Nothing
      writeSTRef refMap $ Map.insert var ref vars
      pure $ RV var ref
-- }}}
makeRefVars :: RefMap s -> Type -> ST s (RefType s) -- {{{
makeRefVars refMap = traverse $ makeRefVar1 refMap
-- }}}
makeRefVarsP :: RefMap s -> Problem -> ST s (RefProblem s) -- {{{
makeRefVarsP refMap (a :?: b) =
  (:?:) <$> makeRefVars refMap a <*> makeRefVars refMap b
-- }}}
unRefVars :: RefType s -> ST s Type -- {{{
unRefVars (B b)            = pure $ B b
unRefVars (List t)         = List <$> unRefVars t
unRefVars (a :-> b)        = (:->) <$> unRefVars a <*> unRefVars b
unRefVars (V (RV var ref)) = maybe (pure $ V var) unRefVars =<< readSTRef ref
-- }}}

unify1ST :: Type -> Type -> Either Error ([Type], Subst)
unify1ST a b = unifyST $ P [a :?: b]

unifyST :: Problems -> Either Error ([Type], Subst)
unifyST (P ps) = runST do
  refMap <- newSTRef []
  ps'    <- traverse (makeRefVarsP refMap) ps
  res'   <- runExceptT $ unifyLoopST [] (P ps')
  case res' of
    Left err  -> pure $ Left err
    Right res -> fmap Right $
      (,) <$> traverse (\(a :?: _) -> unRefVars a) (toList ps')
          <*> traverse unRefVars res

unifyLoopST :: RefSubst s -> RefProblems s -> ExceptT Error (ST s) (RefSubst s)
unifyLoopST σ (P Empty)      = pure σ
unifyLoopST σ (P (p :<| ps)) = case p of
  -- decompose arrows and lists
  List a    :?:  List b   -> unifyLoopST σ $ P $ ps :|> a :?: b
  (a :-> b) :?: (c :-> d) -> unifyLoopST σ $ P $ ps :|> a :?: c :|> b :?: d

  -- base types must be the same
  B a :?: B b | a == b -> unifyLoopST σ $ P ps

  -- see below
  V α :?: b   -> unifyVarST α b σ $ P ps
  a   :?: V β -> unifyVarST β a σ $ P ps

  -- otherwise, constructor clash e.g. INT ≟ (A :-> B)
  a :?: b -> throwError =<< Clash <$> lift (unRefVars a) <*> lift (unRefVars b)

unifyVarST :: RefVar s -> RefType s -> RefSubst s -> RefProblems s ->
              ExceptT Error (ST s) (RefSubst s)
unifyVarST α@(RV v ref) b σ (P ps) =
  lift (readSTRef ref) >>= \case
    Just a  -> unifyLoopST σ $ P $ ps :|> a :?: b
    Nothing
      | b == V α   -> unifyLoopST σ (P ps)
      | occurs α b -> throwError . Occurs v =<< lift (unRefVars b)
      | otherwise  -> do
          lift $ writeSTRef ref (Just b)
          unifyLoopST (Map.insert v b σ) (P ps)

-- vim: set fdm=marker fdl=0 :
