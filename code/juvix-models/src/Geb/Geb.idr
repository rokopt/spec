module Geb.Geb

import Library.FunctionsAndRelations
import RefinedSExp.SExp
import Library.Decidability
import RefinedSExp.SExp

%default total

-- | A "Language" (short in this case for "programming language") is a category
-- | which is capable of performing computation and can be defined solely by
-- | computation.  It can be viewed as having morphisms which represent
-- | computable functions with computably-representable effects.
-- |
-- | By "capable of performing computation", we mean that Gödel's
-- | incompleteness theorems apply to the category.  In other words, it can
-- | express metalogic; we could also say that it can reflect itself, in that
-- | it can define functions on its own expressions.  (So perhaps we might
-- | say something like "computable metacategory" rather than "programming
-- | language".)
-- |
-- | A language is unsuitable as a metalogic if it is inconsistent -- if its
-- | operational semantics allow non-termination, or if it has any partial
-- | functions.  Of course, one consequence of Gödel's incompleteness theorems
-- | is that we can never be sure that there _are_ any languages that are
-- | suitable as metalogics in that sense!
-- |
-- | So there is a minimal programming language, with this definition:  just
-- | what is required for Gödel's incompleteness theorems to apply.  There is
-- | also a maximal programming language:  the universal Turing machine,
-- | with non-terminating and partial functions.

public export
data LanguageRep : Type where
  MinimalRep : LanguageRep

public export
data Language : LanguageRep -> Type where
  -- | The minimal programming language required for Gödel's incompleteness
  -- | theorems to apply.  We treat this abstractly, as a category with
  -- | an initial object, a terminal object, finite products and coproducts,
  -- | an object which we interpret as the type of representations of the
  -- | language's objects and morphisms, and a decidable equality on those
  -- | representations.  The combination of products, coproducts, and decidable
  -- | equality gives us the ability to perform substitution, which in turn
  -- | allows us to represent function application -- the fundamental
  -- | computation in any programming language.
  Minimal : Language MinimalRep

public export
language : (r : LanguageRep) -> Language r
language MinimalRep = Minimal

public export
languageRepCorrect : {r : LanguageRep} -> (l : Language r) -> language r = l
languageRepCorrect Minimal = Refl

public export
languageUnique : {r : LanguageRep} -> (l, l' : Language r) -> l = l'
languageUnique l l' = trans (sym $ languageRepCorrect l) (languageRepCorrect l')

-------------------------
---- Minimal objects ----
-------------------------

-- | Every programming language (using the Geb definition) has an initial
-- | object, a terminal object, finite products and coproducts, an object
-- | which we interpret as the type of representations of the language's
-- | objects and morphisms, and a decidable equality on those
-- | representations.  This is enough to perform substitution on
-- | representations.
-- |
-- | Note that we are _not_ assuming exponential objects yet -- for example,
-- | the minimal language does not have any first-class functions, and
-- | primitive recursion has only first-order functions.

-- | Well-typed representations of common objects.
public export
data MinimalObjectRep : Type where
  InitialRep : MinimalObjectRep
  TerminalRep : MinimalObjectRep
  ProductRep : MinimalObjectRep -> MinimalObjectRep -> MinimalObjectRep
  CoproductRep : MinimalObjectRep -> MinimalObjectRep -> MinimalObjectRep
  ExpressionRep : MinimalObjectRep

public export
data MinimalMorphismRep : Type where

public export
data MinimalExpressionRep : Type where
  MinimalObjectExp : MinimalObjectRep -> MinimalExpressionRep
  MinimalMorphismExp : MinimalMorphismRep -> MinimalExpressionRep

-- | Minimal objects, indexed by their representations.
public export
data MinimalObject : MinimalObjectRep -> Type where
  Initial : MinimalObject InitialRep
  Terminal : MinimalObject TerminalRep
  Product : {r, r' : MinimalObjectRep} ->
    MinimalObject r -> MinimalObject r' -> MinimalObject (ProductRep r r')
  Coproduct : {r, r' : MinimalObjectRep} ->
    MinimalObject r -> MinimalObject r' -> MinimalObject (CoproductRep r r')
  Expression : MinimalObject ExpressionRep

-- | Translate a representation to a minimal object.
public export
minimalObject : (r : MinimalObjectRep) -> MinimalObject r
minimalObject InitialRep = Initial
minimalObject TerminalRep = Terminal
minimalObject (ProductRep o o') =
  Product (minimalObject o) (minimalObject o')
minimalObject (CoproductRep o o') =
  Coproduct (minimalObject o) (minimalObject o')
minimalObject ExpressionRep = Expression

public export
minimalObjectRepCorrect : {r : MinimalObjectRep} -> (o : MinimalObject r) ->
  minimalObject r = o
minimalObjectRepCorrect Initial = Refl
minimalObjectRepCorrect Terminal = Refl
minimalObjectRepCorrect (Product o o') =
  rewrite minimalObjectRepCorrect o in
  rewrite minimalObjectRepCorrect o' in
  Refl
minimalObjectRepCorrect (Coproduct o o') =
  rewrite minimalObjectRepCorrect o in
  rewrite minimalObjectRepCorrect o' in
  Refl
minimalObjectRepCorrect Expression = Refl

public export
minimalObjectUnique : {r : MinimalObjectRep} -> (o, o' : MinimalObject r) ->
  o = o'
minimalObjectUnique o o' =
  trans (sym $ minimalObjectRepCorrect o) (minimalObjectRepCorrect o')

-- | Minimal morphisms, indexed by their representations, as well as
-- | by their domains and codomains.
public export
data MinimalMorphism :
  MinimalMorphismRep -> {domainRep, codomainRep : MinimalObjectRep} ->
  (domain : MinimalObject domainRep) ->
  (codomain : MinimalObject codomainRep) ->
  Type where

public export
minimalMorphismRepDomain : MinimalMorphismRep -> MinimalObjectRep
minimalMorphismRepDomain _ impossible

public export
minimalMorphismRepCodomain : MinimalMorphismRep -> MinimalObjectRep
minimalMorphismRepCodomain _ impossible

public export
minimalMorphismDomain :
  (r : MinimalMorphismRep) -> MinimalObject (minimalMorphismRepDomain r)
minimalMorphismDomain r = minimalObject (minimalMorphismRepDomain r)

public export
minimalMorphismCodomain :
  (r : MinimalMorphismRep) -> MinimalObject (minimalMorphismRepCodomain r)
minimalMorphismCodomain r = minimalObject (minimalMorphismRepCodomain r)

-- | Translate a representation to a minimal morphism.
public export
minimalMorphism : (r : MinimalMorphismRep) ->
  MinimalMorphism r (minimalMorphismDomain r) (minimalMorphismCodomain r)
minimalMorphism _ impossible

public export
minimalMorphismRepCorrect : {r : MinimalMorphismRep} ->
  (m : MinimalMorphism r
    (minimalMorphismDomain r) (minimalMorphismCodomain r)) ->
  minimalMorphism r = m
minimalMorphismRepCorrect _ impossible

public export
minimalMorphismUnique : {r : MinimalMorphismRep} ->
  (m, m': MinimalMorphism r
    (minimalMorphismDomain r) (minimalMorphismCodomain r)) ->
  m = m'
minimalMorphismUnique m m' =
  trans (sym $ minimalMorphismRepCorrect m) (minimalMorphismRepCorrect m')

-----------------------------------------------------------------------------
---- The interpretation into Idris-2 of the minimal programming language ----
-----------------------------------------------------------------------------

public export
interpretMinimalObject : {r : MinimalObjectRep} -> MinimalObject r -> Type
interpretMinimalObject Initial = Void
interpretMinimalObject Terminal = ()
interpretMinimalObject (Product o o') =
  (interpretMinimalObject o, interpretMinimalObject o')
interpretMinimalObject (Coproduct o o') =
  Either (interpretMinimalObject o) (interpretMinimalObject o')
interpretMinimalObject Expression = MinimalExpressionRep

public export
interpretMinimalObjectRep : MinimalObjectRep -> Type
interpretMinimalObjectRep r = interpretMinimalObject (minimalObject r)

public export
interpretMinimalMorphism :
  {r : MinimalMorphismRep} ->
  (m: MinimalMorphism r
    (minimalMorphismDomain r) (minimalMorphismCodomain r)) ->
  interpretMinimalObject (minimalMorphismDomain r) ->
  interpretMinimalObject (minimalMorphismCodomain r)
interpretMinimalMorphism m impossible

public export
interpretMinimalMorphismRep : (r : MinimalMorphismRep) ->
  interpretMinimalObject (minimalMorphismDomain r) ->
  interpretMinimalObject (minimalMorphismCodomain r)
interpretMinimalMorphismRep r = interpretMinimalMorphism (minimalMorphism r)

------------------------------------------------------------
---- Term reduction in the minimal programming language ----
------------------------------------------------------------

-- | Terms are used to define operational semantics for the category-theoretical
-- | representations of programming languages.  We have a well-typed
-- | representation of terms in Idris defined by the interpretation of objects
-- | as types -- together with the notion of function application, which we
-- | do not have in the category-theoretical representation.

public export
data MinimalTerm : MinimalExpressionRep -> Type where
  FullyEvaluatedTerm : (r : MinimalObjectRep) ->
    interpretMinimalObjectRep r -> MinimalTerm (MinimalObjectExp r)
  Application : (r : MinimalMorphismRep) ->
    MinimalTerm (MinimalMorphismExp r) ->
    MinimalTerm (MinimalObjectExp (minimalMorphismRepDomain r)) ->
    MinimalTerm (MinimalObjectExp (minimalMorphismRepCodomain r))

--------------------------------------------
---- S-expression representation of Geb ----
--------------------------------------------

-- | Having a representation of all Geb expressions as S-expressions allows
-- | us to define, check, and interpret them in uniform ways, without having
-- | to use custom ADTs in different metalanguages (where in this case
-- | "metalanguages" refers to programming languages in which we might interpret
-- | Geb expressions, such as Haskell, Rust, or Juvix).
public export
data GebAtom : Type where
  -- | The notion of a language itself.
  GALanguage : GebAtom

  -- | The minimal programming language.
  GAMinimal : GebAtom

  -- | The notion of an object of any programming language.
  GAObject : GebAtom

  -- | Objects common to all programming languages.
  GAInitial : GebAtom
  GATerminal : GebAtom
  GAProduct : GebAtom
  GACoproduct : GebAtom
  GAExpression : GebAtom

  -- | The notion of a morphism of any programming language.
  GAMorphism : GebAtom

  -- | Morphisms common to all programming languages.

  -- | The notion of a term of any programming language.
  GATerm : GebAtom

  -- | Terms common to all programming languages.
  GAEvaluatedTerm : GebAtom
  GAApplication : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GALanguage = 0
gaEncode GAMinimal = 1
gaEncode GAObject = 2
gaEncode GAInitial = 3
gaEncode GATerminal = 4
gaEncode GAProduct = 5
gaEncode GACoproduct = 6
gaEncode GAExpression = 7
gaEncode GAMorphism = 8
gaEncode GATerm = 9
gaEncode GAEvaluatedTerm = 10
gaEncode GAApplication = 11

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GALanguage
gaDecode 1 = Just GAMinimal
gaDecode 2 = Just GAObject
gaDecode 3 = Just GAInitial
gaDecode 4 = Just GATerminal
gaDecode 5 = Just GAProduct
gaDecode 6 = Just GACoproduct
gaDecode 7 = Just GAExpression
gaDecode 8 = Just GAMorphism
gaDecode 9 = Just GATerm
gaDecode 10 = Just GAEvaluatedTerm
gaDecode 11 = Just GAApplication
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GALanguage = Refl
gaDecodeEncodeIsJust GAMinimal = Refl
gaDecodeEncodeIsJust GAObject = Refl
gaDecodeEncodeIsJust GAInitial = Refl
gaDecodeEncodeIsJust GATerminal = Refl
gaDecodeEncodeIsJust GAProduct = Refl
gaDecodeEncodeIsJust GACoproduct = Refl
gaDecodeEncodeIsJust GAExpression = Refl
gaDecodeEncodeIsJust GAMorphism = Refl
gaDecodeEncodeIsJust GATerm = Refl
gaDecodeEncodeIsJust GAEvaluatedTerm = Refl
gaDecodeEncodeIsJust GAApplication = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GALanguage = "Language"
gebAtomToString GAMinimal = "Minimal"
gebAtomToString GAObject = "Object"
gebAtomToString GAInitial = "Initial"
gebAtomToString GATerminal = "Terminal"
gebAtomToString GAProduct = "Product"
gebAtomToString GACoproduct = "Coproduct"
gebAtomToString GAExpression = "Expression"
gebAtomToString GAMorphism = "Morphism"
gebAtomToString GATerm = "Term"
gebAtomToString GAEvaluatedTerm = "EvaluatedTerm"
gebAtomToString GAApplication = "Application"

public export
Show GebAtom where
  show a = ":" ++ gebAtomToString a

public export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

public export
Eq GebAtom where
  (==) = gaEq

public export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq a a' with (decEq (gaEncode a) (gaEncode a'))
  gaDecEq a a' | Yes eq = Yes $
    justInjective $
      trans
        (sym (gaDecodeEncodeIsJust a))
        (trans (cong gaDecode eq) (gaDecodeEncodeIsJust a'))
  gaDecEq a a' | No neq = No $ \aeq => neq $ cong gaEncode aeq

public export
DecEq GebAtom where
  decEq = gaDecEq

public export
GebSExp : Type
GebSExp = SExp GebAtom

public export
GebSList : Type
GebSList = SList GebAtom

public export
Show GebSExp where
  show = fst (sexpShows show)

public export
Show GebSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
gsDecEq : DecEqPred GebSExp
gsDecEq = sexpDecEq gaDecEq

public export
gslDecEq : DecEqPred GebSList
gslDecEq = slistDecEq gaDecEq

public export
DecEq GebSExp where
  decEq = gsDecEq

public export
DecEq GebSList where
  decEq = gslDecEq

public export
Eq GebSExp using decEqToEq where
  (==) = (==)

public export
Ord GebSExp where
  (<) = sexpLessThan (<)

public export
Ord GebSList where
  (<) = slistLessThan (<)

----------------------------------------------------------------------------
---- Translation between (well-typed) Geb expressions and S-expressions ----
----------------------------------------------------------------------------

public export
data GebExpressionClass : Type where
  LanguageClass : GebExpressionClass
  ObjectClass : GebExpressionClass
  MorphismClass : GebExpressionClass
  TermClass : GebExpressionClass

public export
gebClassToExp : GebExpressionClass -> GebSExp
gebClassToExp LanguageClass = $^ GALanguage
gebClassToExp ObjectClass = $^ GAObject
gebClassToExp MorphismClass = $^ GAMorphism
gebClassToExp TermClass = $^ GATerm

public export
gebExpToClass : GebSExp -> Maybe GebExpressionClass
gebExpToClass (GALanguage $* []) = Just LanguageClass
gebExpToClass (GAObject $* []) = Just ObjectClass
gebExpToClass (GAMorphism $* []) = Just MorphismClass
gebExpToClass (GATerm $* []) = Just TermClass
gebExpToClass _ = Nothing

export
gebExpressionClassRepresentationComplete :
  (c : GebExpressionClass) -> gebExpToClass (gebClassToExp c) = Just c
gebExpressionClassRepresentationComplete LanguageClass = Refl
gebExpressionClassRepresentationComplete ObjectClass = Refl
gebExpressionClassRepresentationComplete MorphismClass = Refl
gebExpressionClassRepresentationComplete TermClass = Refl

public export
gebLanguageRepToExp : LanguageRep -> GebSExp
gebLanguageRepToExp MinimalRep = $^ GAMinimal

public export
gebExpToLanguageRep : GebSExp -> Maybe LanguageRep
gebExpToLanguageRep (GAMinimal $* []) = Just MinimalRep
gebExpToLanguageRep _ = Nothing

public export
gebLanguageRepRepresentationComplete : (r : LanguageRep) ->
  gebExpToLanguageRep (gebLanguageRepToExp r) = Just r
gebLanguageRepRepresentationComplete MinimalRep = Refl

public export
gebExpToLanguage : GebSExp -> Maybe (r : LanguageRep ** Language r)
gebExpToLanguage x = case gebExpToLanguageRep x of
  Just r => Just (r ** language r)
  Nothing => Nothing

public export
gebLanguageRepresentationComplete : {r : LanguageRep} -> (l : Language r) ->
  gebExpToLanguage (gebLanguageRepToExp r) = Just (r ** l)
gebLanguageRepresentationComplete {r} l =
  rewrite gebLanguageRepRepresentationComplete r in
  rewrite languageRepCorrect l in
  Refl

public export
gebMinimalObjectRepToExp : MinimalObjectRep -> GebSExp
gebMinimalObjectRepToExp InitialRep = $^ GAInitial
gebMinimalObjectRepToExp TerminalRep = $^ GATerminal
gebMinimalObjectRepToExp (ProductRep r r') =
  GAProduct $* [gebMinimalObjectRepToExp r, gebMinimalObjectRepToExp r']
gebMinimalObjectRepToExp (CoproductRep r r') =
  GACoproduct $* [gebMinimalObjectRepToExp r, gebMinimalObjectRepToExp r']
gebMinimalObjectRepToExp ExpressionRep = $^ GAExpression

public export
gebExpToMinimalObjectRep : GebSExp -> Maybe MinimalObjectRep
gebExpToMinimalObjectRep (GAInitial $* []) = Just InitialRep
gebExpToMinimalObjectRep (GATerminal $* []) = Just TerminalRep
gebExpToMinimalObjectRep (GAProduct $* [r, r']) =
  case (gebExpToMinimalObjectRep r, gebExpToMinimalObjectRep r') of
    (Just o, Just o') => Just $ ProductRep o o'
    _ => Nothing
gebExpToMinimalObjectRep (GACoproduct $* [r, r']) =
  case (gebExpToMinimalObjectRep r, gebExpToMinimalObjectRep r') of
    (Just o, Just o') => Just $ CoproductRep o o'
    _ => Nothing
gebExpToMinimalObjectRep (GAExpression $* []) = Just ExpressionRep
gebExpToMinimalObjectRep _ = Nothing

public export
gebMinimalObjectRepRepresentationComplete : (r : MinimalObjectRep) ->
  gebExpToMinimalObjectRep (gebMinimalObjectRepToExp r) = Just r
gebMinimalObjectRepRepresentationComplete InitialRep = Refl
gebMinimalObjectRepRepresentationComplete TerminalRep = Refl
gebMinimalObjectRepRepresentationComplete (ProductRep r r') =
  rewrite gebMinimalObjectRepRepresentationComplete r in
  rewrite gebMinimalObjectRepRepresentationComplete r' in
  Refl
gebMinimalObjectRepRepresentationComplete (CoproductRep r r') =
  rewrite gebMinimalObjectRepRepresentationComplete r in
  rewrite gebMinimalObjectRepRepresentationComplete r' in
  Refl
gebMinimalObjectRepRepresentationComplete ExpressionRep = Refl

public export
gebExpToMinimalObject :
  GebSExp -> Maybe (r : MinimalObjectRep ** MinimalObject r)
gebExpToMinimalObject x = case gebExpToMinimalObjectRep x of
  Just r => Just (r ** minimalObject r)
  Nothing => Nothing

public export
gebMinimalObjectRepresentationComplete :
  {r : MinimalObjectRep} -> (o : MinimalObject r) ->
  gebExpToMinimalObject (gebMinimalObjectRepToExp r) = Just (r ** o)
gebMinimalObjectRepresentationComplete {r} o =
  rewrite gebMinimalObjectRepRepresentationComplete r in
  rewrite minimalObjectRepCorrect o in
  Refl

public export
gebMinimalMorphismRepToExp : MinimalMorphismRep -> GebSExp
gebMinimalMorphismRepToExp _ impossible

public export
gebExpToMinimalMorphismRep : GebSExp -> Maybe MinimalMorphismRep
gebExpToMinimalMorphismRep _ = Nothing

public export
gebMinimalMorphismRepRepresentationComplete : (r : MinimalMorphismRep) ->
  gebExpToMinimalMorphismRep (gebMinimalMorphismRepToExp r) = Just r
gebMinimalMorphismRepRepresentationComplete _ impossible

public export
gebExpToMinimalMorphism :
  GebSExp -> Maybe (r : MinimalMorphismRep **
    MinimalMorphism r (minimalMorphismDomain r) (minimalMorphismCodomain r))
gebExpToMinimalMorphism x = case gebExpToMinimalMorphismRep x of
  Just r => Just (r ** minimalMorphism r)
  Nothing => Nothing

public export
gebMinimalMorphismRepresentationComplete :
  {r : MinimalMorphismRep} ->
  (m : MinimalMorphism r
    (minimalMorphismDomain r) (minimalMorphismCodomain r)) ->
  gebExpToMinimalMorphism (gebMinimalMorphismRepToExp r) = Just (r ** m)
gebMinimalMorphismRepresentationComplete {r} m impossible
  {-
  rewrite gebMinimalMorphismRepRepresentationComplete r in
  rewrite minimalMorphismRepCorrect m in
  Refl
  -}

public export
gebMinimalTermToExp : {r : MinimalExpressionRep} -> MinimalTerm r -> GebSExp
gebMinimalTermToExp t = ?gebMinimalTermToExp_hole

public export
gebExpToMinimalTerm :
  GebSExp -> Maybe (r : MinimalExpressionRep ** MinimalTerm r)
gebExpToMinimalTerm x = ?gebExpToMinimalTerm_hole

public export
gebMinimalTermRepresentationComplete :
  {r : MinimalExpressionRep} -> (t : MinimalTerm r) ->
  gebExpToMinimalTerm (gebMinimalTermToExp {r} t) = Just (r ** t)
gebMinimalTermRepresentationComplete t =
  ?gebMinimalTermRepresentationComplete_hole
