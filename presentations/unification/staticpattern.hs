-- imports, etc {{{
{-# LANGUAGE
    BlockArguments, DeriveLift, DeriveTraversable, FlexibleInstances,
    LambdaCase, OverloadedLists, OverloadedStrings, ParallelListComp,
    PatternSynonyms, QuasiQuotes, TemplateHaskell, TupleSections,
    TypeSynonymInstances, ViewPatterns
  #-}

import Prelude hiding (lex)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import Data.Foldable
import Data.Maybe
import Data.Void

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import qualified Text.PrettyPrint.HughesPJ as PP
import Text.PrettyPrint.HughesPJ ((<+>))
import qualified Text.Parsec.String as Pa
import qualified Text.Parsec as Pa
import Text.Parsec ((<?>))

import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
-- }}}

data BaseTerm = Bool Bool | Nil | Cons
  deriving (Eq, Show, Lift)

data Term' v
  = Meta v | Bound Var | Base BaseTerm
  | Abs Var (Term' v) | Term' v :@: Term' v             -- functions
  | Term' v :&: Term' v | Fst (Term' v) | Snd (Term' v) -- pairs
  deriving (Eq, Show, Functor, Foldable, Traversable, Lift)

newtype Meta = M String deriving (Eq, Ord, Show, Lift)
newtype Var  = V String deriving (Eq, Ord, Show, Lift)

type Term = Term' Meta

type Subst' u v = Map u (Term' v)
type Subst = Subst' Meta Meta

data Problem' v = Term' v :?: Term' v
  deriving (Eq, Show, Functor, Foldable, Traversable, Lift)
newtype Problems' v = P (Seq (Problem' v)) -- queue of equations
  deriving (Eq, Show, Functor, Foldable, Traversable)
instance Lift v => Lift (Problems' v) where -- {{{
  liftTyped (P ps) = [||P (Seq.fromList $$(liftTyped (toList ps)))||] -- }}}

type Problem  = Problem'  Meta
type Problems = Problems' Meta

data Error = Occurs Meta Term
           | Clash Term Term
           | NotPattern Term
           | ArgLengthMismatch Head [Term] [Term]
  deriving Show

-- splitting applications into a head and a spine
-- e.g. α x y z ==> (α, [x, y, z])
data Head' v = MetaH v | BoundH Var | BaseH BaseTerm
  deriving (Eq, Show, Functor, Foldable, Traversable, Lift)

type Head = Head' Meta

pattern (:@@:) :: Head' v -> [Term' v] -> Term' v
pattern f :@@: ss <- (split -> Just (f, ss))
  where f :@@: ss =  foldl (:@:) (unHead f) ss

{-# COMPLETE Abs, (:@@:), (:&:), Fst, Snd #-}

unHead :: Head' v -> Term' v
unHead (MetaH  α) = Meta α
unHead (BoundH x) = Bound x
unHead (BaseH  b) = Base b

split :: Term' v -> Maybe (Head' v, [Term' v])
split = go [] where
  go args (Meta  α) = Just (MetaH α,  args)
  go args (Bound x) = Just (BoundH x, args)
  go args (Base  b) = Just (BaseH b,  args)
  go args (f :@: x) = go (x : args) f
  go _    _         = Nothing


-- @unAbs (Just n)@: try to peel off exactly @n@ outer lambdas
-- @unAbs Nothing@: peel off as many as there are, but at least one
unAbs :: Maybe Int -> Term' v -> Maybe ([Var], Term' v)
unAbs = go [] where
  go xs (Just 0) t         = Just (reverse xs, t)
  go xs n        (Abs x t) = go (x:xs) (subtract 1 <$> n) t
  go xs Nothing  t         = Just (reverse xs, t)
  go _  _        _         = Nothing

pattern Abss :: [Var] -> Term' v -> Term' v
pattern Abss xs t <- (unAbs Nothing -> Just (xs@(_:_), t))
  where Abss xs t =  foldr Abs t xs

{-# COMPLETE Abss, (:@@:), (:&:), Fst, Snd #-}


-- infinite stream of names different from the ones given
namesAvoiding :: Set String -> [String]
namesAvoiding vars = filter (\x -> x `notElem` vars) names where
  names   = [base : i | i <- indices, base <- ['a'..'z']]
  indices = "" : map show [(0 :: Integer) ..]

namesAvoidingP :: Problems -> [String]
namesAvoidingP (P ps) =
  namesAvoiding $ foldMap (\(s :?: t) -> allVars s <> allVars t) ps

allVars :: Term -> Set String
allVars (Meta  (M α)) = [α]
allVars (Bound (V x)) = [x]
allVars (Base  _)     = []
allVars (Abs (V x) t) = Set.insert x $ allVars t
allVars (s :@: t)     = allVars s <> allVars t
allVars (s :&: t)     = allVars s <> allVars t
allVars (Fst t)       = allVars t
allVars (Snd t)       = allVars t


-- quasiquoter {{{
lex :: Pa.Parser a -> Pa.Parser a
lex p = p <* Pa.spaces

tok :: String -> Pa.Parser ()
tok = void . lex . Pa.try . Pa.string

word :: String -> Pa.Parser ()
word str = void $ lex $ Pa.try $
  Pa.string str <* Pa.notFollowedBy Pa.alphaNum

parseTerm :: Pa.Parser Term
parseTerm =
      Abss <$> (tok "\\" *> Pa.many1 (V <$> ident) <* tok ".") <*> parseTerm
  <|> Fst  <$> (word "fst" *> aterm)
  <|> Snd  <$> (word "snd" *> aterm)
  <|> foldl1 (:@:) <$> Pa.many1 aterm
 where
  aterm =
         tuple
    <|>  Base      <$> base
    <|> (Meta  . M <$> (Pa.char '?' *> ident) <?> "metavariable")
    <|> (Bound . V <$> ident                  <?> "bound variable")
  ident = lex $ (:) <$> Pa.letter <*> Pa.many Pa.alphaNum
  base  =
        Bool True  <$ word "true"
    <|> Bool False <$ word "false"
    <|> Nil        <$ word "nil"
    <|> Cons       <$ word "cons"
  tuple = tok "(" *> Pa.chainr1 parseTerm ((:&:) <$ tok ",") <* tok ")"

parseProblem :: Pa.Parser Problem
parseProblem = do
  a <- parseTerm
  _ <- tok "≐" <|> tok "==="
  b <- parseTerm
  pure $ a :?: b

parseProblems :: Pa.Parser Problems
parseProblems = P . Seq.fromList <$> parseProblem `Pa.sepEndBy` tok ";"

tm, pb :: QuasiQuoter
tm = parsecQQ parseTerm     [t|Term|]
pb = parsecQQ parseProblems [t|Problems|]

parsecQQ :: Lift a => Pa.Parser a -> Q Type -> QuasiQuoter
parsecQQ p ty = QuasiQuoter qexp undefined undefined undefined where
  qexp str = case Pa.parse (Pa.spaces *> p <* Pa.eof) "quote" str of
    Left err -> fail $ show err
    Right x  -> [|x :: $ty|]

-- }}}
-- pretty printing {{{
class Pretty a where
  ppPrec :: Int -> a -> PP.Doc

ppr :: Pretty a => a -> PP.Doc
ppr = ppPrec 0

instance Pretty Void where ppPrec _ = absurd
instance Pretty Meta where ppPrec _ (M x) = "?" <> PP.text x
instance Pretty Var  where ppPrec _ (V x) = PP.text x

instance Pretty BaseTerm where
  ppPrec _ = \case
    Bool b -> PP.text $ if b then "true" else "false"
    Nil    -> "nil"
    Cons   -> "cons"

instance Pretty a => Pretty (Term' a) where
  ppPrec d = \case
    Abss xs t -> PP.maybeParens (d > 0) $
      PP.sep [PP.hcat ["\\", PP.hsep $ map ppr xs, "."], ppr t]
    f :@@: [] -> ppr f
    f :@@: ss -> PP.maybeParens (d > 9) $
      PP.sep [ppr f, PP.sep $ map (ppPrec 10) ss]
    s :&: t -> PP.parens $ PP.sep $ PP.punctuate "," $ map ppr $ s : getPairs t
      where getPairs (s :&: t) = s : getPairs t
            getPairs t         = [t]
    Fst t -> PP.maybeParens (d > 9) $
      PP.sep ["fst", ppPrec 10 t]
    Snd t -> PP.maybeParens (d > 9) $
      PP.sep ["snd", ppPrec 10 t]

instance Pretty a => Pretty (Head' a) where
  ppPrec _ = \case
    MetaH  α -> ppr α
    BoundH x -> ppr x
    BaseH  b -> ppr b


instance (Pretty u, Pretty v) => Pretty (Subst' u v) where
  ppPrec _ =
    PP.braces . PP.sep . PP.punctuate ";" . map ppPair . Map.toList
    where ppPair (x, t) = PP.sep [ppr x, "|->", ppPrec 10 t]

instance Pretty Error where
  ppPrec _ (Occurs i t) =
    PP.hang (PP.sep ["metavariable", ppr i, "occurs in"]) 2 $ ppr t
  ppPrec _ (Clash s t) =
    PP.hang "type constructor clash:" 2 $
      PP.sep [ppr s <+> "and", ppr t]
  ppPrec _ (NotPattern t) =
    PP.hang "not a pattern:" 2 $ ppr t
  ppPrec _ (ArgLengthMismatch h ss ts) =
    PP.hang "argument length mismatch between" 2 $
      PP.sep [ppPrec 10 (h :@@: ss) <+> "and",
              ppPrec 10 (h :@@: ts)]

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  ppPrec d = either (ppPrec d) (ppPrec d)

instance Pretty a => Pretty (Problem' a) where
  ppPrec d (a :?: b) = PP.maybeParens (d > 0) $
    PP.hang (ppPrec 9 a <+> "≐") 2 (ppPrec 9 b)

instance Pretty a => Pretty (Problems' a) where
  ppPrec _ (P ps) = PP.braces $ PP.sep $ PP.punctuate ";" $ map ppr $ toList ps
-- }}}

--------------------------------------------------------------------------------

-- apply a term substitution
-- assumes no accidental captures because that's not the point of this example
subst :: Ord v => Subst' Var v -> Term' v -> Term' v
subst σ = \case
  α@(Meta _) -> α
  Bound i    -> fromMaybe (Bound i) $ Map.lookup i σ
  b@(Base _) -> b
  Abs x t    -> Abs x $ subst σ t
  s :@: t    -> subst σ s :@: subst σ t
  s :&: t    -> subst σ s :&: subst σ t
  Fst t      -> Fst $ subst σ t
  Snd t      -> Snd $ subst σ t

etaContract :: Term -> Term
etaContract (Abss xs (t :@@: yxs))
  | let len = length yxs - length xs,
    (ys, xs') <- splitAt len yxs,
    map Bound xs == xs'
  = t :@@: ys
etaContract t = t

--------------------------------------------------------------------------------

unify1 :: Term -> Term -> Either Error Subst
unify1 a b = unify $ P [a :?: b]

unify :: Problems -> Either Error Subst
unify ps = evalStateT (unifyLoop [] ps) (namesAvoidingP ps)

type Unify = StateT [String] (Either Error)

unifyLoop :: Subst -> Problems -> Unify Subst
unifyLoop σ (P ps) = foldlM unifyLoop1 σ ps

unifyLoop1 :: Subst -> Problem -> Unify Subst
unifyLoop1 σ (s₀ :?: t₀) = case devar σ s₀ :?: devar σ t₀ of
  Abs x s :?: Abs y t
    | x == y    -> unifyLoop1 σ $ s :?: t
    | otherwise -> unifyLoop1 σ $ s :?: subst [(y, Bound x)] t

  Abs x s :?: t       -> unifyLoop1 σ $ s               :?: (t :@: Bound x)
  s       :?: Abs y t -> unifyLoop1 σ $ (s :@: Bound y) :?: t

  s :?: t -> cases σ s t

cases :: Subst -> Term -> Term -> Unify Subst
-- non-variable cases
cases σ (a :&: b) (c :&: d) = unifyLoop σ $ P [a :?: c, b :?: d]
cases σ (Fst s)   (Fst t)   = unifyLoop1 σ $ s :?: t
cases σ (Snd s)   (Snd t)   = unifyLoop1 σ $ s :?: t
-- variables
cases σ (MetaH α :@@: ss) (MetaH β :@@: ts) = flexflex   σ α ss β ts
cases σ (MetaH α :@@: ss) t                 = flexrigid  σ α ss t
cases σ s                 (MetaH β :@@: ts) = flexrigid  σ β ts s
cases σ (f       :@@: ss) (g       :@@: ts) = rigidrigid σ f ss g ts
cases _ s t = throwError $ Clash s t

flexflex :: Subst -> Meta -> [Term] -> Meta -> [Term] -> Unify Subst
flexflex σ α ss β ts = do
  xs <- patternArgs α ss
  ys <- patternArgs β ts
  if α == β then
    flexflex1 σ α xs ys
  else
    flexflex2 σ α xs β ys

flexflex1 :: Subst -> Meta -> [Var] -> [Var] -> Unify Subst
flexflex1 σ α xs ys = do
  unless (length xs == length ys) do
    throwError $ ArgLengthMismatch (MetaH α) (map Bound xs) (map Bound ys)
  -- all the vars shared by both
  let args = catMaybes $ zipWith (\x y -> Bound x <$ guard (x == y)) xs ys
  γ <- MetaH . M <$> fresh
  pure $ [(α, Abss xs $ γ :@@: args)] <> σ

flexflex2 :: Subst -> Meta -> [Var] -> Meta -> [Var] -> Unify Subst
flexflex2 σ α xs β ys = do
  let yset = Set.fromList ys
  let zs = map Bound $ filter (`elem` yset) xs
  γ <- MetaH . M <$> fresh
  pure $ [(α, Abss xs $ γ :@@: zs), (β, Abss ys $ γ :@@: zs)] <> σ

flexrigid :: Subst -> Meta -> [Term] -> Term -> Unify Subst
flexrigid σ α ss t = do
  xs <- patternArgs α ss
  when (occurs σ α t) do throwError $ Occurs α t
  proj (Set.fromList xs) ([(α, Abss xs t)] <> σ) t

proj :: Set Var -> Subst -> Term -> Unify Subst
proj xs σ t₀ = case devar σ t₀ of
  Abs x t          -> proj (Set.insert x xs) σ t
  s :&: t          -> do σ' <- proj xs σ s; proj xs σ' t
  Fst s            -> proj xs σ s
  Snd s            -> proj xs σ s
  BaseH  _ :@@: ss -> foldlM (proj xs) σ ss
  BoundH x :@@: ss
    | x `elem` xs -> foldlM (proj xs) σ ss
    | otherwise   ->
        -- in the paper, this is @fail@
        -- but here i am assuming that unbound variables are constants
        foldlM (proj xs) σ ss
  MetaH α :@@: ss -> do
    ys <- patternArgs α ss
    let zs = map Bound $ filter (`elem` xs) ys
    γ <- MetaH . M <$> fresh
    pure $ [(α, Abss ys $ γ :@@: zs)] <> σ

rigidrigid :: Subst -> Head -> [Term] -> Head -> [Term] -> Unify Subst
rigidrigid σ h ss k ts = do
  unless (h == k) do throwError $ Clash (unHead h) (unHead k)
  unless (length ss == length ts) do throwError $ ArgLengthMismatch h ss ts
  foldlM unifyLoop1 σ $ zipWith (:?:) ss ts

fresh :: Unify String
fresh = state \ ~(n:ns) -> (n, ns)

patternArgs :: Meta -> [Term] -> Unify [Var]
patternArgs _ (traverse toVar -> Just vars)
  | length vars == length (Set.fromList vars)
  = pure vars
patternArgs α args = throwError $ NotPattern $ MetaH α :@@: args

toVar :: Term -> Maybe Var
toVar (etaContract -> Bound x) = Just x
toVar _                        = Nothing

devar :: Subst -> Term -> Term
devar σ (MetaH α :@@: ss)
  | let len = length ss,
    Just t' <- Map.lookup α σ,
    Just (xs, t) <- unAbs (Just len) t',
    let θ = Map.fromList $ zip xs ss
  = devar σ $ subst θ t
devar _ t = t

occurs :: Subst -> Meta -> Term -> Bool
occurs σ α = any \β -> α == β || maybe False (occurs σ α) (Map.lookup β σ)
