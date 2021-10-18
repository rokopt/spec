module Geb.Geb

import Library.FunctionsAndRelations
import RefinedSExp.SExp
import Library.Decidability
import RefinedSExp.SExp
import Data.SortedSet
import Data.SortedMap

%default total

--------------------------------------------
---- S-expression representation of Geb ----
--------------------------------------------

-- | Having a representation of all Geb expressions as S-expressions allows
-- | us to define, check, and interpret them in uniform ways, without having
-- | to use custom ADTs in different metalanguages (where in this case
-- | "metalanguages" refers to programming languages in which we might interpret
-- |
-- | We begin with this definition even though it might not be clear before
-- | programming languages have been defined below, because we will use the
-- | existence of an S-expression representation to define some functions
-- | (such as decidable equalities and Show instances) below.  These reflect
-- | the reasons for having an S-expression representation of types (objects),
-- | functions (morphisms), and terms (operational semantics given by
-- | interpretation of morphisms as computable functions with effects) within
-- | a compiler.
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
  GAIdentity : GebAtom
  GACompose : GebAtom
  GAFromInitial : GebAtom
  GAToTerminal : GebAtom

  -- | The notion of a term of any programming language.
  GATerm : GebAtom

  -- | Terms common to all programming languages.
  GAEvaluatedTerm : GebAtom
  GAMorphismTerm : GebAtom
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
gaEncode GAMorphismTerm = 11
gaEncode GAApplication = 12
gaEncode GAFromInitial = 13
gaEncode GAToTerminal = 14
gaEncode GAIdentity = 15
gaEncode GACompose = 16

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
gaDecode 11 = Just GAMorphismTerm
gaDecode 12 = Just GAApplication
gaDecode 13 = Just GAFromInitial
gaDecode 14 = Just GAToTerminal
gaDecode 15 = Just GAIdentity
gaDecode 16 = Just GACompose
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
gaDecodeEncodeIsJust GAMorphismTerm = Refl
gaDecodeEncodeIsJust GAApplication = Refl
gaDecodeEncodeIsJust GAFromInitial = Refl
gaDecodeEncodeIsJust GAToTerminal = Refl
gaDecodeEncodeIsJust GAIdentity = Refl
gaDecodeEncodeIsJust GACompose = Refl

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
gebAtomToString GAMorphismTerm = "MorphismTerm"
gebAtomToString GAApplication = "Application"
gebAtomToString GAFromInitial = "FromInitial"
gebAtomToString GAToTerminal = "ToTerminal"
gebAtomToString GAIdentity = "Identity"
gebAtomToString GACompose = "Compose"

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

public export
GebSet : Type
GebSet = SortedSet GebSExp

public export
gebSet : GebSList -> GebSet
gebSet = fromList

public export
GebMap : Type
GebMap = SortedMap GebAtom GebSList

public export
gebMap : List (GebAtom, GebSList) -> GebMap
gebMap = fromList

-- | One of the concepts for which we have an S-expression representation is
-- | the class of S-expression itself -- whether an S-expression represents
-- | a language, for example, or an object, morphism, or term.

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
Show GebExpressionClass where
  show c = show (gebClassToExp c)

----------------------------------------------------------------
---- General definition of programming language / metalogic ----
----------------------------------------------------------------

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
-- | language".)  A combination of products, coproducts, and decidable
-- | equality gives us the ability to perform substitution, which in turn
-- | allows us to represent function application -- the fundamental
-- | computation in any programming language.
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
-- |
-- | Our definitions of languages below all take the form of a
-- | category-theoretical, point-free (termless) definition of syntax and
-- | type system, and an operational definition of semantics using an
-- | interpretation of objects as the types and morphisms as the functions
-- | of a programming language which does have terms.  The functions of the
-- | language are general computable functions with effects, the terms are
-- | S-expressions, and the types are specifications of the domains,
-- | codomains, input-output behavior, and the effects of functions.
public export
data Language : Type where
  MinimalLanguage : Language

public export
gebLanguageToExp : Language -> GebSExp
gebLanguageToExp MinimalLanguage = $^ GAMinimal

public export
gebExpToLanguage : GebSExp -> Maybe Language
gebExpToLanguage (GAMinimal $* []) = Just MinimalLanguage
gebExpToLanguage _ = Nothing

public export
gebLanguageRepresentationComplete : (r : Language) ->
  gebExpToLanguage (gebLanguageToExp r) = Just r
gebLanguageRepresentationComplete MinimalLanguage = Refl

public export
Show Language where
  show l = show (gebLanguageToExp l)

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
data MinimalObject : Type where
  Initial : MinimalObject
  Terminal : MinimalObject
  Product : MinimalObject -> MinimalObject -> MinimalObject
  Coproduct : MinimalObject -> MinimalObject -> MinimalObject
  Expression : MinimalObject

public export
gebMinimalObjectToExp : MinimalObject -> GebSExp
gebMinimalObjectToExp Initial = $^ GAInitial
gebMinimalObjectToExp Terminal = $^ GATerminal
gebMinimalObjectToExp (Product r r') =
  GAProduct $* [gebMinimalObjectToExp r, gebMinimalObjectToExp r']
gebMinimalObjectToExp (Coproduct r r') =
  GACoproduct $* [gebMinimalObjectToExp r, gebMinimalObjectToExp r']
gebMinimalObjectToExp Expression = $^ GAExpression

public export
gebExpToMinimalObject : GebSExp -> Maybe MinimalObject
gebExpToMinimalObject (GAInitial $* []) = Just Initial
gebExpToMinimalObject (GATerminal $* []) = Just Terminal
gebExpToMinimalObject (GAProduct $* [r, r']) =
  case (gebExpToMinimalObject r, gebExpToMinimalObject r') of
    (Just o, Just o') => Just $ Product o o'
    _ => Nothing
gebExpToMinimalObject (GACoproduct $* [r, r']) =
  case (gebExpToMinimalObject r, gebExpToMinimalObject r') of
    (Just o, Just o') => Just $ Coproduct o o'
    _ => Nothing
gebExpToMinimalObject (GAExpression $* []) = Just Expression
gebExpToMinimalObject _ = Nothing

public export
gebMinimalObjectRepresentationComplete : (r : MinimalObject) ->
  gebExpToMinimalObject (gebMinimalObjectToExp r) = Just r
gebMinimalObjectRepresentationComplete Initial = Refl
gebMinimalObjectRepresentationComplete Terminal = Refl
gebMinimalObjectRepresentationComplete (Product r r') =
  rewrite gebMinimalObjectRepresentationComplete r in
  rewrite gebMinimalObjectRepresentationComplete r' in
  Refl
gebMinimalObjectRepresentationComplete (Coproduct r r') =
  rewrite gebMinimalObjectRepresentationComplete r in
  rewrite gebMinimalObjectRepresentationComplete r' in
  Refl
gebMinimalObjectRepresentationComplete Expression = Refl

public export
Show MinimalObject where
  show o = show (gebMinimalObjectToExp o)

export
minimalObjectDecEq : DecEqPred MinimalObject
minimalObjectDecEq =
  encodingDecEq
    gebMinimalObjectToExp
    gebExpToMinimalObject
    gebMinimalObjectRepresentationComplete
    decEq

public export
DecEq MinimalObject where
  decEq = minimalObjectDecEq

mutual
  public export
  data MinimalMorphism : Type where
    Identity : MinimalObject -> MinimalMorphism
    Compose : (g, f : MinimalMorphism) ->
      {auto composable :
        (minimalMorphismCodomain f) = (minimalMorphismDomain g)} ->
      MinimalMorphism
    FromInitial : MinimalObject -> MinimalMorphism
    ToTerminal : MinimalObject -> MinimalMorphism
    ProductIntro : (f, g : MinimalMorphism) ->
      {auto domainsMatch :
        (minimalMorphismDomain f) = (minimalMorphismDomain g)} ->
      MinimalMorphism
    ProductElimLeft : (a, b : MinimalObject) -> MinimalMorphism
    ProductElimRight : (a, b : MinimalObject) -> MinimalMorphism
    CoproductElim : (f, g : MinimalMorphism) ->
      {auto codomainsMatch :
        (minimalMorphismCodomain f) = (minimalMorphismCodomain g)} ->
      MinimalMorphism
    CoproductIntroLeft : (a, b : MinimalObject) -> MinimalMorphism
    CoproductIntroRight : (a, b : MinimalObject) -> MinimalMorphism
    ExpressionIntro : MinimalExpression -> MinimalMorphism
    ExpressionElim : (exp, exp', eqCase, neqCase : MinimalMorphism) ->
      {auto expDomainsMatch :
        (minimalMorphismDomain exp) = (minimalMorphismDomain exp')} ->
      {auto eqDomainMatches :
        (minimalMorphismDomain exp) = (minimalMorphismDomain eqCase)} ->
      {auto neqDomainMatches :
        (minimalMorphismDomain exp) = (minimalMorphismDomain neqCase)} ->
      {auto eqCodomainsMatch :
        (minimalMorphismCodomain eqCase) = (minimalMorphismCodomain neqCase)} ->
      MinimalMorphism

  public export
  data MinimalExpression : Type where
    MinimalObjectExp : MinimalObject -> MinimalExpression
    MinimalMorphismExp : MinimalMorphism -> MinimalExpression

  public export
  minimalMorphismDomain : MinimalMorphism -> MinimalObject
  minimalMorphismDomain (Identity object) = object
  minimalMorphismDomain (Compose g f) = minimalMorphismDomain f
  minimalMorphismDomain (FromInitial _) = Initial
  minimalMorphismDomain (ToTerminal domain) = domain
  minimalMorphismDomain (ProductIntro f g) = minimalMorphismDomain f
  minimalMorphismDomain (ProductElimLeft a b) = Product a b
  minimalMorphismDomain (ProductElimRight a b) = Product a b
  minimalMorphismDomain (CoproductElim f g) =
    Coproduct (minimalMorphismDomain f) (minimalMorphismDomain g)
  minimalMorphismDomain (CoproductIntroLeft a b) = a
  minimalMorphismDomain (CoproductIntroRight a b) = b
  minimalMorphismDomain (ExpressionIntro _) = Terminal
  minimalMorphismDomain (ExpressionElim exp _ _ _) = minimalMorphismDomain exp

  public export
  minimalMorphismCodomain : MinimalMorphism -> MinimalObject
  minimalMorphismCodomain (Identity object) = object
  minimalMorphismCodomain (Compose g f) = minimalMorphismCodomain g
  minimalMorphismCodomain (FromInitial codomain) = codomain
  minimalMorphismCodomain (ToTerminal _) = Terminal
  minimalMorphismCodomain (ProductIntro f g) =
    Product (minimalMorphismCodomain f) (minimalMorphismCodomain g)
  minimalMorphismCodomain (ProductElimLeft a b) = a
  minimalMorphismCodomain (ProductElimRight a b) = b
  minimalMorphismCodomain (CoproductElim f g) = minimalMorphismCodomain f
  minimalMorphismCodomain (CoproductIntroLeft a b) = Coproduct a b
  minimalMorphismCodomain (CoproductIntroRight a b) = Coproduct a b
  minimalMorphismCodomain (ExpressionIntro _) = Expression
  minimalMorphismCodomain (ExpressionElim _ _ eqCase _) =
    minimalMorphismCodomain eqCase

mutual
  public export
  gebMinimalMorphismToExp : MinimalMorphism -> GebSExp
  gebMinimalMorphismToExp (Identity object) =
    GAIdentity $* [gebMinimalObjectToExp object]
  gebMinimalMorphismToExp (Compose g f) =
    GACompose $* [gebMinimalMorphismToExp g, gebMinimalMorphismToExp f]
  gebMinimalMorphismToExp (FromInitial codomain) =
    GAFromInitial $* [gebMinimalObjectToExp codomain]
  gebMinimalMorphismToExp (ToTerminal domain) =
    GAToTerminal $* [gebMinimalObjectToExp domain]
  gebMinimalMorphismToExp _ = ?gebMinimalMorphismToExp_hole

  public export
  gebExpToMinimalMorphism : GebSExp -> Maybe MinimalMorphism
  gebExpToMinimalMorphism (GAIdentity $* [objectExp]) =
    case gebExpToMinimalObject objectExp of
      Just object => Just $ Identity object
      _ => Nothing
  gebExpToMinimalMorphism (GACompose $* [gExp, fExp]) =
    case (gebExpToMinimalMorphism gExp, gebExpToMinimalMorphism fExp) of
      (Just g, Just f) =>
        case (minimalObjectDecEq
          (minimalMorphismCodomain f) (minimalMorphismDomain g)) of
            Yes composable => Just $ Compose g f {composable}
            No _ => Nothing
      _ => Nothing
  gebExpToMinimalMorphism (GAFromInitial $* [codomainExp]) =
    case gebExpToMinimalObject codomainExp of
      Just codomain => Just $ FromInitial codomain
      _ => Nothing
  gebExpToMinimalMorphism (GAToTerminal $* [domainExp]) =
    case gebExpToMinimalObject domainExp of
      Just domain => Just $ ToTerminal domain
      _ => Nothing
  gebExpToMinimalMorphism _ = Nothing

  public export
  gebMinimalMorphismRepresentationComplete : (r : MinimalMorphism) ->
    gebExpToMinimalMorphism (gebMinimalMorphismToExp r) = Just r
  gebMinimalMorphismRepresentationComplete (Identity object) =
    rewrite gebMinimalObjectRepresentationComplete object in
    Refl
  gebMinimalMorphismRepresentationComplete (Compose g f {composable}) =
    rewrite gebMinimalMorphismRepresentationComplete g in
    rewrite gebMinimalMorphismRepresentationComplete f in
    rewrite composable in
    rewrite decEqRefl minimalObjectDecEq (minimalMorphismDomain g) in
    rewrite uip composable _ in
    Refl
  gebMinimalMorphismRepresentationComplete (FromInitial codomain) =
    rewrite gebMinimalObjectRepresentationComplete codomain in
    Refl
  gebMinimalMorphismRepresentationComplete (ToTerminal domain) =
    rewrite gebMinimalObjectRepresentationComplete domain in
    Refl
  gebMinimalMorphismRepresentationComplete _ =
    ?gebMinimalMorphismRepresentationComplete_hole

  public export
  Show MinimalMorphism where
    show m = show (gebMinimalMorphismToExp m)

  export
  minimalMorphismDecEq : DecEqPred MinimalMorphism
  minimalMorphismDecEq =
    encodingDecEq
      gebMinimalMorphismToExp
      gebExpToMinimalMorphism
      gebMinimalMorphismRepresentationComplete
      decEq

  public export
  DecEq MinimalMorphism where
    decEq = minimalMorphismDecEq

-----------------------------------------------------------------------------
---- The interpretation into Idris-2 of the minimal programming language ----
-----------------------------------------------------------------------------

public export
interpretMinimalObject : MinimalObject -> Type
interpretMinimalObject Initial = Void
interpretMinimalObject Terminal = ()
interpretMinimalObject (Product r r') =
  (interpretMinimalObject r, interpretMinimalObject r')
interpretMinimalObject (Coproduct r r') =
  Either (interpretMinimalObject r) (interpretMinimalObject r')
interpretMinimalObject Expression = MinimalExpression

public export
interpretMinimalMorphismDomain : MinimalMorphism -> Type
interpretMinimalMorphismDomain r =
  interpretMinimalObject (minimalMorphismDomain r)

public export
interpretMinimalMorphismCodomain : MinimalMorphism -> Type
interpretMinimalMorphismCodomain r =
  interpretMinimalObject (minimalMorphismCodomain r)

public export
interpretMinimalMorphismType : MinimalMorphism -> Type
interpretMinimalMorphismType r =
  interpretMinimalMorphismDomain r -> interpretMinimalMorphismCodomain r

public export
interpretMinimalMorphism : (r : MinimalMorphism) ->
  interpretMinimalMorphismType r
interpretMinimalMorphism (Identity o) x = x
interpretMinimalMorphism (Compose g f {composable}) x =
  interpretMinimalMorphism g $
    replace {p=interpretMinimalObject} composable $
      interpretMinimalMorphism f x
interpretMinimalMorphism (FromInitial _) x = void x
interpretMinimalMorphism (ToTerminal _) _ = ()
interpretMinimalMorphism _ _ = ?interpretMinimalMorphism_hole

-----------------------------------
---- Correctness of reflection ----
-----------------------------------

public export
minimalObjectQuote :
  MinimalObject -> interpretMinimalObject Expression
minimalObjectQuote o = ?minimalObjectReflection_hole

public export
minimalObjectUnquote :
  interpretMinimalObject Expression -> MinimalObject
minimalObjectUnquote x = ?minimalObjectUnquote_hole

export
minimalObjectUnquoteQuoteCorrect :
  (r : MinimalObject) -> minimalObjectUnquote (minimalObjectQuote r) = r
minimalObjectUnquoteQuoteCorrect r = ?minimalObjectUnquoteQuoteCorrect_hole

export
minimalObjectQuoteUnquoteCorrect :
  (x : interpretMinimalObject Expression) ->
  minimalObjectQuote (minimalObjectUnquote x) = x
minimalObjectQuoteUnquoteCorrect x = ?minimalObjectQuoteUnquoteCorrect_hole

public export
minimalMorphismQuote :
  MinimalMorphism -> interpretMinimalObject Expression
minimalMorphismQuote m = ?minimalMorphismReflection_hole

public export
minimalMorphismUnquote : interpretMinimalObject Expression ->
  MinimalMorphism
minimalMorphismUnquote x = ?minimalMorphismUnquote_hole

export
minimalMorphismUnquoteQuoteCorrect : (r : MinimalMorphism) ->
  minimalMorphismUnquote (minimalMorphismQuote r) = r
minimalMorphismUnquoteQuoteCorrect r =
  ?minimalMorphismUnquoteQuoteCorrect_hole

export
minimalMorphismQuoteUnquoteCorrect :
  (x : interpretMinimalObject Expression) ->
  minimalMorphismQuote (minimalMorphismUnquote x) = x
minimalMorphismQuoteUnquoteCorrect x = ?minimalMorphismQuoteUnquoteCorrect_hole

------------------------------------------------------
---- Morphism transformations ("compiler passes") ----
------------------------------------------------------

public export
MinimalMorphismTransform : Type
MinimalMorphismTransform = MinimalMorphism -> MinimalMorphism

-- | A correct morphism transformation preserves the morphism's domain.
public export
MinimalMorphismTransformDomainCorrect : MinimalMorphismTransform -> Type
MinimalMorphismTransformDomainCorrect transform = (m : MinimalMorphism) ->
  interpretMinimalMorphismDomain (transform m) =
    interpretMinimalMorphismDomain m

-- | A correct morphism transformation preserves the morphism's codomain.
public export
MinimalMorphismTransformCodomainCorrect : MinimalMorphismTransform -> Type
MinimalMorphismTransformCodomainCorrect transform = (m : MinimalMorphism) ->
  interpretMinimalMorphismCodomain (transform m) =
    interpretMinimalMorphismCodomain m

-- | A correct morphism transformation preserves extensional equality.
public export
MinimalMorphismTransformCorrect : (transform : MinimalMorphismTransform) ->
  (domainTransformCorrect :
    MinimalMorphismTransformDomainCorrect transform) ->
  (codomainTransformCorrect :
    MinimalMorphismTransformCodomainCorrect transform) ->
  Type
MinimalMorphismTransformCorrect
  transform domainTransformCorrect codomainTransformCorrect =
    (m : MinimalMorphism) ->
    (x : interpretMinimalMorphismDomain m) ->
      (rewrite sym (codomainTransformCorrect m) in
       interpretMinimalMorphism (transform m)
         (rewrite domainTransformCorrect m in x)) =
       interpretMinimalMorphism m x

------------------------------------------------------------
---- Term reduction in the minimal programming language ----
------------------------------------------------------------

-- | Terms are used to define operational semantics for the category-theoretical
-- | representations of programming languages.  We have a well-typed
-- | representation of terms in Idris defined by the interpretation of objects
-- | as types -- together with the notion of function application, which we
-- | do not have in the category-theoretical representation.

public export
data MinimalTermType : Type where
  MinimalTypeTerm : (type : MinimalObject) -> MinimalTermType
  MinimalMorphismTerm : (domain, codomain : MinimalObject) -> MinimalTermType

mutual
  public export
  data MinimalFullyAppliedTerm : MinimalTermType -> Type where
    UnappliedMorphismTerm : (morphism : MinimalMorphism) ->
      MinimalFullyAppliedTerm $
        MinimalMorphismTerm
          (minimalMorphismDomain morphism)
          (minimalMorphismCodomain morphism)
    UnitTerm : MinimalFullyAppliedTerm $ MinimalTypeTerm Terminal

  public export
  data MinimalTerm : MinimalTermType -> Type where
    FullyEvaluatedTerm : {type : MinimalTermType} ->
      MinimalFullyAppliedTerm type -> MinimalTerm type
    Application : {domain, codomain : MinimalObject} ->
      MinimalTerm (MinimalMorphismTerm domain codomain) ->
      MinimalTerm (MinimalTypeTerm domain) ->
      MinimalTerm (MinimalTypeTerm codomain)

mutual
  public export
  gebMinimalTermToExp : {type : MinimalTermType} -> MinimalTerm type -> GebSExp
  gebMinimalTermToExp t = ?gebMinimalTermToExp_hole

  public export
  gebExpToMinimalTerm :
    GebSExp -> Maybe (type : MinimalTermType ** MinimalTerm type)
  gebExpToMinimalTerm x = ?gebExpToMinimalTerm_hole

  public export
  gebMinimalTermRepresentationComplete :
    {type : MinimalTermType} -> (term : MinimalTerm type) ->
    gebExpToMinimalTerm (gebMinimalTermToExp {type} term) = Just (type ** term)
  gebMinimalTermRepresentationComplete term =
    ?gebMinimalTermRepresentationComplete_hole

public export
(type : MinimalTermType) => Show (MinimalTerm type) where
  show term = show (gebMinimalTermToExp term)

mutual
  public export
  interpretMinimalTermType : MinimalTermType -> Type
  interpretMinimalTermType type = ?interpretMinimalTermType_hole

  public export
  interpretMinimalTerm : {type : MinimalTermType} ->
    (term : MinimalTerm type) -> interpretMinimalTermType type
  interpretMinimalTerm {type} term = ?interpretMinimalTerm_hole

public export
minimalMorphismToTerm : (m : MinimalMorphism) ->
  MinimalTerm $
    MinimalMorphismTerm
      (minimalMorphismDomain m)
      (minimalMorphismCodomain m)
minimalMorphismToTerm m = FullyEvaluatedTerm $ UnappliedMorphismTerm m

public export
bigStepMinimalTermReduction : {type : MinimalTermType} -> MinimalTerm type ->
  MinimalFullyAppliedTerm type
bigStepMinimalTermReduction {type} term = ?bigStepMinimalTermReduction_hole

public export
bigStepMinimalTermReductionCorrect :
  {type : MinimalTermType} -> (term : MinimalTerm type) ->
  interpretMinimalTerm (FullyEvaluatedTerm (bigStepMinimalTermReduction term)) =
    interpretMinimalTerm term
bigStepMinimalTermReductionCorrect {type} term =
  ?bigStepMinimalTermReductionCorrect_hole

public export
smallStepMinimalTermReduction : {type : MinimalTermType} -> MinimalTerm type ->
  Either (MinimalFullyAppliedTerm type) (MinimalTerm type)
smallStepMinimalTermReduction {type} term = ?smallStepMinimalTermReduction_hole

public export
data SmallStepMinimalTermReductionCompletes : {type : MinimalTermType} ->
  (term : MinimalTerm type) -> (reduced : MinimalFullyAppliedTerm type) -> Type
  where
    SmallStepMinimalReductionLastStep : {type : MinimalTermType} ->
      {term : MinimalTerm type} -> {reduced : MinimalFullyAppliedTerm type} ->
      smallStepMinimalTermReduction term = Left reduced ->
      SmallStepMinimalTermReductionCompletes term reduced
    SmallStepMinimalReductionPreviousStep : {type : MinimalTermType} ->
      {term, intermediateTerm : MinimalTerm type} ->
      {reduced : MinimalFullyAppliedTerm type} ->
      smallStepMinimalTermReduction term = Right intermediateTerm ->
      SmallStepMinimalTermReductionCompletes intermediateTerm reduced ->
      SmallStepMinimalTermReductionCompletes term reduced

public export
smallStepMinimalTermReductionCompletes :
  {type : MinimalTermType} -> (term : MinimalTerm type) ->
  DPair
    (MinimalFullyAppliedTerm type)
    (SmallStepMinimalTermReductionCompletes term)
smallStepMinimalTermReductionCompletes {type} term =
  ?smallStepMinimalTermReductionCompletes_hole

public export
smallStepMinimalTermReductionCorrect :
  {type : MinimalTermType} -> (term : MinimalTerm type) ->
  interpretMinimalTerm (FullyEvaluatedTerm
    (fst (smallStepMinimalTermReductionCompletes term))) =
      interpretMinimalTerm term
smallStepMinimalTermReductionCorrect {type} term =
  ?smallStepMinimalTermReductionCorrect_hole

public export
minimalTermReductionsConsistent :
  {type : MinimalTermType} -> (term : MinimalTerm type) ->
  bigStepMinimalTermReduction term =
    snd (smallStepMinimalTermReductionCompletes term)
minimalTermReductionsConsistent term = ?minimalTermReductionsConsistent_hole
