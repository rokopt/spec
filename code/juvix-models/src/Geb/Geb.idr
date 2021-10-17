module Geb.Geb

import Library.FunctionsAndRelations
import RefinedSExp.SExp
import Library.Decidability
import RefinedSExp.SExp

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
data LanguageRep : Type where
  MinimalRep : LanguageRep

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
Show LanguageRep where
  show l = show (gebLanguageRepToExp l)

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
Show MinimalObjectRep where
  show o = show (gebMinimalObjectRepToExp o)

export
minimalObjectRepDecEq : DecEqPred MinimalObjectRep
minimalObjectRepDecEq =
  encodingDecEq
    gebMinimalObjectRepToExp
    gebExpToMinimalObjectRep
    gebMinimalObjectRepRepresentationComplete
    decEq

public export
DecEq MinimalObjectRep where
  decEq = minimalObjectRepDecEq

mutual
  public export
  data MinimalMorphismRep : Type where
    IdentityRep : MinimalObjectRep -> MinimalMorphismRep
    ComposeRep : (g, f : MinimalMorphismRep) ->
      {auto composable : AreDecEq Geb.Geb.minimalObjectRepDecEq
        (minimalMorphismRepCodomain f) (minimalMorphismRepDomain g)} ->
      MinimalMorphismRep
    FromInitialRep : MinimalObjectRep -> MinimalMorphismRep
    ToTerminalRep : MinimalObjectRep -> MinimalMorphismRep

  public export
  minimalMorphismRepDomain : MinimalMorphismRep -> MinimalObjectRep
  minimalMorphismRepDomain (IdentityRep objectRep) = objectRep
  minimalMorphismRepDomain (ComposeRep g f) = minimalMorphismRepDomain f
  minimalMorphismRepDomain (FromInitialRep _) = InitialRep
  minimalMorphismRepDomain (ToTerminalRep domain) = domain

  public export
  minimalMorphismRepCodomain : MinimalMorphismRep -> MinimalObjectRep
  minimalMorphismRepCodomain (IdentityRep objectRep) = objectRep
  minimalMorphismRepCodomain (ComposeRep g f) = minimalMorphismRepCodomain g
  minimalMorphismRepCodomain (FromInitialRep codomain) = codomain
  minimalMorphismRepCodomain (ToTerminalRep _) = TerminalRep

mutual
  public export
  gebMinimalMorphismRepToExp : MinimalMorphismRep -> GebSExp
  gebMinimalMorphismRepToExp (IdentityRep objectRep) =
    GAIdentity $* [gebMinimalObjectRepToExp objectRep]
  gebMinimalMorphismRepToExp (ComposeRep g f) =
    GACompose $* [gebMinimalMorphismRepToExp g, gebMinimalMorphismRepToExp f]
  gebMinimalMorphismRepToExp (FromInitialRep codomainRep) =
    GAFromInitial $* [gebMinimalObjectRepToExp codomainRep]
  gebMinimalMorphismRepToExp (ToTerminalRep domainRep) =
    GAToTerminal $* [gebMinimalObjectRepToExp domainRep]

  public export
  gebExpToMinimalMorphismRep : GebSExp -> Maybe MinimalMorphismRep
  gebExpToMinimalMorphismRep (GAIdentity $* [objectExp]) =
    case gebExpToMinimalObjectRep objectExp of
      Just objectRep => Just $ IdentityRep objectRep
      _ => Nothing
  gebExpToMinimalMorphismRep (GACompose $* [gExp, fExp]) =
    case (gebExpToMinimalMorphismRep gExp, gebExpToMinimalMorphismRep fExp) of
      (Just gRep, Just fRep) =>
        case (minimalObjectRepDecEq
          (minimalMorphismRepCodomain fRep) (minimalMorphismRepDomain gRep)) of
            Yes composable =>
              Just $ ComposeRep gRep fRep
                {composable=(
                    rewrite composable in
                    DecEqReturnsYes {deq=minimalObjectRepDecEq} $
                      decEqRefl minimalObjectRepDecEq
                        (minimalMorphismRepDomain gRep))}
            No _ => Nothing
      _ => Nothing
  gebExpToMinimalMorphismRep (GAFromInitial $* [codomainExp]) =
    case gebExpToMinimalObjectRep codomainExp of
      Just codomainRep => Just $ FromInitialRep codomainRep
      _ => Nothing
  gebExpToMinimalMorphismRep (GAToTerminal $* [domainExp]) =
    case gebExpToMinimalObjectRep domainExp of
      Just domainRep => Just $ ToTerminalRep domainRep
      _ => Nothing
  gebExpToMinimalMorphismRep _ = Nothing

  public export
  gebMinimalMorphismRepRepresentationComplete : (r : MinimalMorphismRep) ->
    gebExpToMinimalMorphismRep (gebMinimalMorphismRepToExp r) = Just r
  gebMinimalMorphismRepRepresentationComplete (IdentityRep objectRep) =
    rewrite gebMinimalObjectRepRepresentationComplete objectRep in
    Refl
  gebMinimalMorphismRepRepresentationComplete (ComposeRep g f {composable}) =
    rewrite gebMinimalMorphismRepRepresentationComplete g in
    rewrite gebMinimalMorphismRepRepresentationComplete f in
    rewrite AreDecEqExtract composable in
    rewrite decEqRefl minimalObjectRepDecEq (minimalMorphismRepDomain g) in
    rewrite AreDecEqUnique composable _ in
    Refl
  gebMinimalMorphismRepRepresentationComplete (FromInitialRep codomainRep) =
    rewrite gebMinimalObjectRepRepresentationComplete codomainRep in
    Refl
  gebMinimalMorphismRepRepresentationComplete (ToTerminalRep domainRep) =
    rewrite gebMinimalObjectRepRepresentationComplete domainRep in
    Refl

  public export
  Show MinimalMorphismRep where
    show m = show (gebMinimalMorphismRepToExp m)

  export
  minimalMorphismRepDecEq : DecEqPred MinimalMorphismRep
  minimalMorphismRepDecEq =
    encodingDecEq
      gebMinimalMorphismRepToExp
      gebExpToMinimalMorphismRep
      gebMinimalMorphismRepRepresentationComplete
      decEq

  public export
  DecEq MinimalMorphismRep where
    decEq = minimalMorphismRepDecEq

-----------------------------------------------------------------------------
---- The interpretation into Idris-2 of the minimal programming language ----
-----------------------------------------------------------------------------

public export
data MinimalExpressionRep : Type where
  MinimalObjectExp : MinimalObjectRep -> MinimalExpressionRep
  MinimalMorphismExp : MinimalMorphismRep -> MinimalExpressionRep

public export
interpretMinimalObjectRep : MinimalObjectRep -> Type
interpretMinimalObjectRep InitialRep = Void
interpretMinimalObjectRep TerminalRep = ()
interpretMinimalObjectRep (ProductRep r r') =
  (interpretMinimalObjectRep r, interpretMinimalObjectRep r')
interpretMinimalObjectRep (CoproductRep r r') =
  Either (interpretMinimalObjectRep r) (interpretMinimalObjectRep r')
interpretMinimalObjectRep ExpressionRep = MinimalExpressionRep

public export
interpretMinimalMorphismDomain : MinimalMorphismRep -> Type
interpretMinimalMorphismDomain r =
  interpretMinimalObjectRep (minimalMorphismRepDomain r)

public export
interpretMinimalMorphismCodomain : MinimalMorphismRep -> Type
interpretMinimalMorphismCodomain r =
  interpretMinimalObjectRep (minimalMorphismRepCodomain r)

public export
interpretMinimalMorphismType : MinimalMorphismRep -> Type
interpretMinimalMorphismType r =
  interpretMinimalMorphismDomain r -> interpretMinimalMorphismCodomain r

public export
interpretMinimalMorphismRep : (r : MinimalMorphismRep) ->
  interpretMinimalMorphismType r
interpretMinimalMorphismRep (IdentityRep o) x = x
interpretMinimalMorphismRep (ComposeRep g f {composable}) x =
  interpretMinimalMorphismRep g $
    replace {p=interpretMinimalObjectRep} (AreDecEqExtract composable) $
      interpretMinimalMorphismRep f x
interpretMinimalMorphismRep (FromInitialRep _) x = void x
interpretMinimalMorphismRep (ToTerminalRep _) _ = ()

-----------------------------------
---- Correctness of reflection ----
-----------------------------------

public export
minimalObjectQuote :
  MinimalObjectRep -> interpretMinimalObjectRep ExpressionRep
minimalObjectQuote o = ?minimalObjectReflection_hole

public export
minimalObjectUnquote :
  interpretMinimalObjectRep ExpressionRep -> MinimalObjectRep
minimalObjectUnquote x = ?minimalObjectUnquote_hole

export
minimalObjectUnquoteQuoteCorrect :
  (r : MinimalObjectRep) -> minimalObjectUnquote (minimalObjectQuote r) = r
minimalObjectUnquoteQuoteCorrect r = ?minimalObjectUnquoteQuoteCorrect_hole

export
minimalObjectQuoteUnquoteCorrect :
  (x : interpretMinimalObjectRep ExpressionRep) ->
  minimalObjectQuote (minimalObjectUnquote x) = x
minimalObjectQuoteUnquoteCorrect x = ?minimalObjectQuoteUnquoteCorrect_hole

public export
minimalMorphismQuote :
  MinimalMorphismRep -> interpretMinimalObjectRep ExpressionRep
minimalMorphismQuote m = ?minimalMorphismReflection_hole

public export
minimalMorphismUnquote : interpretMinimalObjectRep ExpressionRep ->
  MinimalMorphismRep
minimalMorphismUnquote x = ?minimalMorphismUnquote_hole

export
minimalMorphismUnquoteQuoteCorrect : (r : MinimalMorphismRep) ->
  minimalMorphismUnquote (minimalMorphismQuote r) = r
minimalMorphismUnquoteQuoteCorrect r =
  ?minimalMorphismUnquoteQuoteCorrect_hole

export
minimalMorphismQuoteUnquoteCorrect :
  (x : interpretMinimalObjectRep ExpressionRep) ->
  minimalMorphismQuote (minimalMorphismUnquote x) = x
minimalMorphismQuoteUnquoteCorrect x = ?minimalMorphismQuoteUnquoteCorrect_hole

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
  MinimalTypeTerm : (type : MinimalObjectRep) -> MinimalTermType
  MinimalMorphismTerm : (domain, codomain : MinimalObjectRep) -> MinimalTermType

mutual
  public export
  data MinimalFullyAppliedTerm : MinimalTermType -> Type where
    UnappliedMorphismTerm : (morphism : MinimalMorphismRep) ->
      MinimalFullyAppliedTerm $
        MinimalMorphismTerm
          (minimalMorphismRepDomain morphism)
          (minimalMorphismRepCodomain morphism)
    UnitTerm : MinimalFullyAppliedTerm $ MinimalTypeTerm TerminalRep

  public export
  data MinimalTerm : MinimalTermType -> Type where
    FullyEvaluatedTerm : {type : MinimalTermType} ->
      MinimalFullyAppliedTerm type -> MinimalTerm type
    Application : {domain, codomain : MinimalObjectRep} ->
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
minimalMorphismToTerm : (m : MinimalMorphismRep) ->
  MinimalTerm $
    MinimalMorphismTerm
      (minimalMorphismRepDomain m)
      (minimalMorphismRepCodomain m)
minimalMorphismToTerm m = FullyEvaluatedTerm $ UnappliedMorphismTerm m

public export
MinimalMorphismTransform : Type
MinimalMorphismTransform = MinimalMorphismRep -> MinimalMorphismRep

-- | A correct morphism transformation preserves the morphism's domain.
public export
MinimalMorphismTransformDomainCorrect : MinimalMorphismTransform -> Type
MinimalMorphismTransformDomainCorrect transform = (m : MinimalMorphismRep) ->
  interpretMinimalMorphismDomain (transform m) =
    interpretMinimalMorphismDomain m

-- | A correct morphism transformation preserves the morphism's codomain.
public export
MinimalMorphismTransformCodomainCorrect : MinimalMorphismTransform -> Type
MinimalMorphismTransformCodomainCorrect transform = (m : MinimalMorphismRep) ->
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
    (m : MinimalMorphismRep) ->
    (x : interpretMinimalMorphismDomain m) ->
      (rewrite sym (codomainTransformCorrect m) in
       interpretMinimalMorphismRep (transform m)
         (rewrite domainTransformCorrect m in x)) =
       interpretMinimalMorphismRep m x
