module Geb.Geb

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap

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
  -- | The notion of sort of refinement -- such as language, object,
  -- | morphism, or even refinement itself.  (One sort of refinement
  -- | is "is a refinement".)
  GARefinementSort : GebAtom
  GALanguageSort : GebAtom
  GASortSort : GebAtom
  GAObjectSort : GebAtom
  GAMorphismSort : GebAtom
  GAExpressionSort : GebAtom

  -- | The notion of a language itself.
  GALanguageRefinement : GebAtom

  -- | The notion of a sort.
  GASortRefinement : GebAtom

  -- | The notion of a refinement.
  GARefinementRefinement : GebAtom

  -- | The notion of an expression.
  GAExpressionRefinement : GebAtom

  -- | The minimal programming language.
  GAMinimal : GebAtom

  -- | Higher-order computable functions.
  GAHigherOrder : GebAtom

  -- | Geb itself.
  GAGeb : GebAtom

  -- | The notion of an object of any programming language.
  GAObjectRefinement : GebAtom

  -- | Objects common to all programming languages.
  GAInitial : GebAtom
  GATerminal : GebAtom
  GAProduct : GebAtom
  GACoproduct : GebAtom
  GAExpressionObject : GebAtom

  GAObjectExpression : GebAtom
  GAMorphismExpression : GebAtom
  GARefinementExpression : GebAtom
  GASortExpression : GebAtom
  GALanguageExpression : GebAtom

  -- | The notion of a morphism of any programming language.
  GAMorphismRefinement : GebAtom

  -- | Morphisms common to all programming languages.
  GAIdentity : GebAtom
  GACompose : GebAtom
  GAFromInitial : GebAtom
  GAToTerminal : GebAtom
  GAProductIntro : GebAtom
  GAProductElimLeft : GebAtom
  GAProductElimRight : GebAtom
  GACoproductElim : GebAtom
  GACoproductIntroLeft : GebAtom
  GACoproductIntroRight : GebAtom
  GAExpressionIntro : GebAtom
  GAExpressionElim : GebAtom

  -- | The notion of a term of any programming language.
  GATerm : GebAtom

  -- | Terms common to all programming languages.
  GAExFalsoTerm : GebAtom
  GAUnitTerm : GebAtom
  GAPairTerm : GebAtom
  GALeftTerm : GebAtom
  GARightTerm : GebAtom
  GAExpressionTerm : GebAtom
  GAMorphismTerm : GebAtom
  GAApplication : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GALanguageRefinement = 0
gaEncode GAMinimal = 1
gaEncode GAObjectRefinement = 2
gaEncode GAInitial = 3
gaEncode GATerminal = 4
gaEncode GAProduct = 5
gaEncode GACoproduct = 6
gaEncode GAObjectExpression = 7
gaEncode GAMorphismRefinement = 8
gaEncode GATerm = 9
gaEncode GAUnitTerm = 10
gaEncode GAMorphismTerm = 11
gaEncode GAApplication = 12
gaEncode GAFromInitial = 13
gaEncode GAToTerminal = 14
gaEncode GAIdentity = 15
gaEncode GACompose = 16
gaEncode GAProductIntro = 17
gaEncode GAProductElimLeft = 18
gaEncode GAProductElimRight = 19
gaEncode GACoproductElim = 20
gaEncode GACoproductIntroLeft = 21
gaEncode GACoproductIntroRight = 22
gaEncode GAExpressionIntro = 23
gaEncode GAExpressionElim = 24
gaEncode GAPairTerm = 25
gaEncode GALeftTerm = 26
gaEncode GARightTerm = 27
gaEncode GAExpressionTerm = 28
gaEncode GAExFalsoTerm = 29
gaEncode GAMorphismExpression = 30
gaEncode GAHigherOrder = 31
gaEncode GAGeb = 32
gaEncode GARefinementRefinement = 33
gaEncode GARefinementSort = 34
gaEncode GALanguageSort = 35
gaEncode GASortSort = 36
gaEncode GASortRefinement = 37
gaEncode GAObjectSort = 38
gaEncode GAMorphismSort = 39
gaEncode GARefinementExpression = 40
gaEncode GASortExpression = 41
gaEncode GALanguageExpression = 42
gaEncode GAExpressionSort = 43
gaEncode GAExpressionRefinement = 44
gaEncode GAExpressionObject = 45

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GALanguageRefinement
gaDecode 1 = Just GAMinimal
gaDecode 2 = Just GAObjectRefinement
gaDecode 3 = Just GAInitial
gaDecode 4 = Just GATerminal
gaDecode 5 = Just GAProduct
gaDecode 6 = Just GACoproduct
gaDecode 7 = Just GAObjectExpression
gaDecode 8 = Just GAMorphismRefinement
gaDecode 9 = Just GATerm
gaDecode 10 = Just GAUnitTerm
gaDecode 11 = Just GAMorphismTerm
gaDecode 12 = Just GAApplication
gaDecode 13 = Just GAFromInitial
gaDecode 14 = Just GAToTerminal
gaDecode 15 = Just GAIdentity
gaDecode 16 = Just GACompose
gaDecode 17 = Just GAProductIntro
gaDecode 18 = Just GAProductElimLeft
gaDecode 19 = Just GAProductElimRight
gaDecode 20 = Just GACoproductElim
gaDecode 21 = Just GACoproductIntroLeft
gaDecode 22 = Just GACoproductIntroRight
gaDecode 23 = Just GAExpressionIntro
gaDecode 24 = Just GAExpressionElim
gaDecode 25 = Just GAPairTerm
gaDecode 26 = Just GALeftTerm
gaDecode 27 = Just GARightTerm
gaDecode 28 = Just GAExpressionTerm
gaDecode 29 = Just GAExFalsoTerm
gaDecode 30 = Just GAMorphismExpression
gaDecode 31 = Just GAHigherOrder
gaDecode 32 = Just GAGeb
gaDecode 33 = Just GARefinementRefinement
gaDecode 34 = Just GARefinementSort
gaDecode 35 = Just GALanguageSort
gaDecode 36 = Just GASortSort
gaDecode 37 = Just GASortRefinement
gaDecode 38 = Just GAObjectSort
gaDecode 39 = Just GAMorphismSort
gaDecode 40 = Just GARefinementExpression
gaDecode 41 = Just GASortExpression
gaDecode 42 = Just GALanguageExpression
gaDecode 43 = Just GAExpressionSort
gaDecode 44 = Just GAExpressionRefinement
gaDecode 45 = Just GAExpressionObject
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GALanguageRefinement = Refl
gaDecodeEncodeIsJust GAMinimal = Refl
gaDecodeEncodeIsJust GAObjectRefinement = Refl
gaDecodeEncodeIsJust GAInitial = Refl
gaDecodeEncodeIsJust GATerminal = Refl
gaDecodeEncodeIsJust GAProduct = Refl
gaDecodeEncodeIsJust GACoproduct = Refl
gaDecodeEncodeIsJust GAObjectExpression = Refl
gaDecodeEncodeIsJust GAMorphismRefinement = Refl
gaDecodeEncodeIsJust GATerm = Refl
gaDecodeEncodeIsJust GAUnitTerm = Refl
gaDecodeEncodeIsJust GAMorphismTerm = Refl
gaDecodeEncodeIsJust GAApplication = Refl
gaDecodeEncodeIsJust GAFromInitial = Refl
gaDecodeEncodeIsJust GAToTerminal = Refl
gaDecodeEncodeIsJust GAIdentity = Refl
gaDecodeEncodeIsJust GACompose = Refl
gaDecodeEncodeIsJust GAProductIntro = Refl
gaDecodeEncodeIsJust GAProductElimLeft = Refl
gaDecodeEncodeIsJust GAProductElimRight = Refl
gaDecodeEncodeIsJust GACoproductElim = Refl
gaDecodeEncodeIsJust GACoproductIntroLeft = Refl
gaDecodeEncodeIsJust GACoproductIntroRight = Refl
gaDecodeEncodeIsJust GAExpressionIntro = Refl
gaDecodeEncodeIsJust GAExpressionElim = Refl
gaDecodeEncodeIsJust GAPairTerm = Refl
gaDecodeEncodeIsJust GALeftTerm = Refl
gaDecodeEncodeIsJust GARightTerm = Refl
gaDecodeEncodeIsJust GAExpressionTerm = Refl
gaDecodeEncodeIsJust GAExFalsoTerm = Refl
gaDecodeEncodeIsJust GAMorphismExpression = Refl
gaDecodeEncodeIsJust GAHigherOrder = Refl
gaDecodeEncodeIsJust GAGeb = Refl
gaDecodeEncodeIsJust GARefinementRefinement = Refl
gaDecodeEncodeIsJust GARefinementSort = Refl
gaDecodeEncodeIsJust GALanguageSort = Refl
gaDecodeEncodeIsJust GASortSort = Refl
gaDecodeEncodeIsJust GASortRefinement = Refl
gaDecodeEncodeIsJust GAObjectSort = Refl
gaDecodeEncodeIsJust GAMorphismSort = Refl
gaDecodeEncodeIsJust GARefinementExpression = Refl
gaDecodeEncodeIsJust GASortExpression = Refl
gaDecodeEncodeIsJust GALanguageExpression = Refl
gaDecodeEncodeIsJust GAExpressionSort = Refl
gaDecodeEncodeIsJust GAExpressionRefinement = Refl
gaDecodeEncodeIsJust GAExpressionObject = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GALanguageRefinement = "Language"
gebAtomToString GAMinimal = "Minimal"
gebAtomToString GAObjectRefinement = "ObjectRefinement"
gebAtomToString GAInitial = "Initial"
gebAtomToString GATerminal = "Terminal"
gebAtomToString GAProduct = "Product"
gebAtomToString GACoproduct = "Coproduct"
gebAtomToString GAObjectExpression = "ObjectExpression"
gebAtomToString GAMorphismRefinement = "MorphismRefinement"
gebAtomToString GATerm = "Term"
gebAtomToString GAUnitTerm = "UnitTerm"
gebAtomToString GAMorphismTerm = "MorphismTerm"
gebAtomToString GAApplication = "Application"
gebAtomToString GAFromInitial = "FromInitial"
gebAtomToString GAToTerminal = "ToTerminal"
gebAtomToString GAIdentity = "Identity"
gebAtomToString GACompose = "Compose"
gebAtomToString GAProductIntro = "ProductIntro"
gebAtomToString GAProductElimLeft = "ProductElimLeft"
gebAtomToString GAProductElimRight = "ProductElimRight"
gebAtomToString GACoproductElim = "CoproductElim"
gebAtomToString GACoproductIntroLeft = "CoproductIntroLeft"
gebAtomToString GACoproductIntroRight = "CoproductIntroRight"
gebAtomToString GAExpressionIntro = "ExpressionIntro"
gebAtomToString GAExpressionElim = "ExpressionElim"
gebAtomToString GAPairTerm = "PairTerm"
gebAtomToString GALeftTerm = "LeftTerm"
gebAtomToString GARightTerm = "RightTerm"
gebAtomToString GAExpressionTerm = "ExpressionTerm"
gebAtomToString GAExFalsoTerm = "ExFalsoTerm"
gebAtomToString GAMorphismExpression = "MorphismExpression"
gebAtomToString GAHigherOrder = "HigherOrder"
gebAtomToString GAGeb = "Geb"
gebAtomToString GARefinementRefinement = "RefinementRefinement"
gebAtomToString GARefinementSort = "RefinementSort"
gebAtomToString GALanguageSort = "LanguageSort"
gebAtomToString GASortSort = "SortSort"
gebAtomToString GASortRefinement = "SortRefinement"
gebAtomToString GAObjectSort = "ObjectSort"
gebAtomToString GAMorphismSort = "MorphismSort"
gebAtomToString GARefinementExpression = "RefinementExpression"
gebAtomToString GASortExpression = "SortExpression"
gebAtomToString GALanguageExpression = "LanguageExpression"
gebAtomToString GAExpressionSort = "ExpressionSort"
gebAtomToString GAExpressionRefinement = "ExpressionRefinement"
gebAtomToString GAExpressionObject = "ExpressionObject"

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

mutual
  -- | Takes no parameters.
  public export
  data Language : GebSExp -> GebSList -> Type where
    Minimal : Language ($^ GAMinimal) []
    HigherOrder : Language ($^ GAHigherOrder) []

  -- | Takes one parameter, a language.
  public export
  data Object : GebSExp -> GebSList -> Type where
    Initial : (lang : GebSExp) -> {auto isLanguage : Language lang []} ->
      Object (GAInitial $*** lang) [lang]
    Terminal : (lang : GebSExp) -> {auto isLanguage : Language lang []} ->
      Object (GATerminal $*** lang) [lang]

    -- | Reflects expressions of each refinement into each language.
    -- | (In particular, this might reflect into language X an expression
    -- | of language Y, or an expression of Geb itself.)
    ExpressionObject : {lang, sort : GebSExp} -> (refinement : GebSExp) ->
      {auto isLanguage : Language lang []} ->
      {auto isSort : Sort sort []} ->
      {auto isRefinement : Refinement refinement [sort]} ->
      Object (GAExpressionObject $* [lang, refinement]) [lang]

  -- | Takes an "implicit" language parameter and two explicit
  -- | object parameters, which must have the same language.
  public export
  data Morphism : GebSExp -> GebSList -> Type where
    Identity : {lang : GebSExp} -> (obj : GebSExp) ->
      {auto isLanguage : Language lang []} ->
      {auto isObj : Object obj [lang]} ->
      Morphism (GAIdentity $*** obj) [lang, obj]
    Compose : {lang, a, b, c : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {auto aObj : Object a [lang]} ->
      {auto bObj : Object b [lang]} ->
      {auto cObj : Object c [lang]} ->
      (g, f : GebSExp) ->
      {auto gMorph : Morphism g [lang, b, c]} ->
      {auto fMorph : Morphism f [lang, a, b]} ->
      Morphism (GACompose $* [g, f]) [lang, a, c]

  -- | Takes no parameters.
  -- | These are "refinement families" (by analogy to "type families").
  public export
  data Sort : GebSExp -> GebSList -> Type where
    SortSort : Sort ($^ GASortSort) []
    RefinementSort : Sort ($^ GARefinementSort) []
    ExpressionSort : Sort ($^ GAExpressionSort) []
    LanguageSort : Sort ($^ GALanguageSort) []
    ObjectSort : Sort ($^ GAObjectSort) []
    MorphismSort : Sort ($^ GAMorphismSort) []

  -- | Takes one parameter, a sort.  Refinements are analogous to types --
  -- | a refinement may be viewed as the type of S-expressions which
  -- | are selected by it (the refinement in this view is a characteristic
  -- | function on S-expressions).
  public export
  data Refinement : GebSExp -> GebSList -> Type where
    SortRefinement : Refinement ($^ GASortRefinement) [$^ GASortSort]
    RefinementRefinement : (s : GebSExp) -> {auto isSort : Sort s []} ->
      Refinement (GARefinementRefinement $*** s) [$^ GARefinementSort]
    ExpressionRefinement : {s : GebSExp} -> {auto isSort : Sort s []} ->
      (r : GebSExp) -> {auto isRefinement : Refinement r [s]} ->
      Refinement (GAExpressionRefinement $* [s, r]) [$^ GAExpressionSort]
    LanguageRefinement :
      Refinement ($^ GALanguageRefinement) [$^ GALanguageSort]
    ObjectRefinement : (lang : GebSExp) ->
      {auto isLanguage : Language lang []} ->
      Refinement (GAObjectRefinement $*** lang) [$^ GAObjectSort]
    MorphismRefinement : {lang : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      (domain, codomain : GebSExp) ->
      {auto domainObj : Object domain [lang]} ->
      {auto codomainObj : Object codomain [lang]} ->
      Refinement
        (GAMorphismRefinement $* [lang, domain, codomain]) [$^ GAMorphismSort]

  -- | Takes two parameters, an "implicit" sort and a refinement of
  -- | that sort.  An expression consists of refinement _constructors_;
  -- | it may be viewed as an S-expression which is selected by its
  -- | refinement parameter.
  public export
  data Expression : GebSExp -> GebSList -> Type where
    SortExpression : (s : GebSExp) -> {auto isSort : Sort s []} ->
      Expression (GASortExpression $*** s) [$^ GASortSort, $^ GASortRefinement]
    RefinementExpression : {s : GebSExp} -> {auto isSort : Sort s []} ->
      (r : GebSExp) ->
      {auto isRefinement :
        Refinement r [GARefinementRefinement $*** s]} ->
      Expression (GARefinementExpression $*** r)
        [$^ GARefinementSort, GARefinementRefinement $*** s]
    LanguageExpression : (lang : GebSExp) ->
      {auto isLanguage : Language lang []} ->
      Expression (GALanguageExpression $*** x)
        [$^ GALanguageSort, $^ GALanguageRefinement]
    ObjectExpression : {lang : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      (object : GebSExp) ->
      {auto isObject : Object object [lang]} ->
      Expression (GAObjectExpression $*** object)
        [$^ GAObjectSort, GAObjectRefinement $*** lang]
    MorphismExpression : {lang, domain, codomain : GebSExp} ->
      {auto isLanguage : Language lang []} ->
      {auto domainObj : Object domain [lang]} ->
      {auto codomainObj : Object codomain [lang]} ->
      (morphism : GebSExp) ->
      {auto isMorphism : Morphism morphism [lang, domain, codomain]} ->
      Expression (GAMorphismExpression $*** morphism)
        [$^ GAMorphismSort, GAMorphismRefinement $* [lang, domain, codomain]]

mutual
  public export
  checkExpression : (expression : GebSExp) -> (refinement : GebSList) ->
    Dec $ Expression expression refinement
  checkExpression x r = ?checkExpression_hole

  public export
  checkExpressionCorrect : {x : GebSExp} -> {l : GebSList} ->
    (exp : Expression x l) -> checkExpression x l = Yes exp
  checkExpressionCorrect {x} {l} exp = ?checkExpressionCorrect_hole

  public export
  checkExpressionUnique : {x : GebSExp} -> {l : GebSList} ->
    (exp, exp' : Expression x l) -> exp = exp'
  checkExpressionUnique {x} {l} exp exp' = ?checkExpressionUnique_hole

mutual
  public export
  interpretObject : {lang : GebSExp} -> {auto isLanguage : Language lang []} ->
    (obj : GebSExp) -> {auto isObject : Object obj [lang]} ->
    Type
  interpretObject {lang} {isLanguage} obj {isObject} = ?interpretObject_hole

  public export
  interpretMorphism : {lang, domain, codomain : GebSExp} ->
    {auto isLanguage : Language lang []} ->
    {auto domainObject : Object domain [lang]} ->
    {auto codomainObject : Object codomain [lang]} ->
    (m : GebSExp) -> {auto isMorphism : Morphism m [lang, domain, codomain]} ->
    (interpretObject {isObject=domainObject} domain ->
     interpretObject {isObject=codomainObject} codomain)
  interpretMorphism {lang} {domain} {codomain} {isLanguage}
    {domainObject} {codomainObject} m {isMorphism} x =
      ?interpretMorphism_hole

  public export
  interpretRefinement : {s : GebSExp} ->
    {auto isSort : Sort s []} ->
    (r : GebSExp) ->
    {auto isRefinement : Refinement r [s]} ->
    (GebSExp -> Bool)
  interpretRefinement {s} r {isSort} {isRefinement} x =
    ?interpretRefinement_hole

{-
  TermSort : GebExpressionSort

public export
gebSortToExp : GebExpressionSort -> GebSExp
gebSortToExp LanguageSort = $^ GALanguageRefinement
gebSortToExp ObjectSort = $^ GAObject
gebSortToExp MorphismSort = $^ GAMorphism
gebSortToExp TermSort = $^ GATerm

public export
gebExpToSort : GebSExp -> Maybe GebExpressionSort
gebExpToSort (GALanguageRefinement $* []) = Just LanguageSort
gebExpToSort (GAObject $* []) = Just ObjectSort
gebExpToSort (GAMorphism $* []) = Just MorphismSort
gebExpToSort (GATerm $* []) = Just TermSort
gebExpToSort _ = Nothing

export
gebExpressionSortRepresentationComplete :
  (c : GebExpressionSort) -> gebExpToSort (gebSortToExp c) = Just c
gebExpressionSortRepresentationComplete LanguageSort = Refl
gebExpressionSortRepresentationComplete ObjectSort = Refl
gebExpressionSortRepresentationComplete MorphismSort = Refl
gebExpressionSortRepresentationComplete TermSort = Refl

public export
Show GebExpressionSort where
  show c = show (gebSortToExp c)

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
-- | the minimal language does not have any first-sort functions, and
-- | primitive recursion has only first-order functions.

-- | Well-typed representations of common objects.
public export
data MinimalObject : Type where
  Initial : MinimalObject
  Terminal : MinimalObject
  Product : MinimalObject -> MinimalObject -> MinimalObject
  Coproduct : MinimalObject -> MinimalObject -> MinimalObject
  ObjectExpression : MinimalObject
  MorphismExpression : MinimalObject -> MinimalObject -> MinimalObject

public export
gebMinimalObjectToExp : MinimalObject -> GebSExp
gebMinimalObjectToExp Initial = $^ GAInitial
gebMinimalObjectToExp Terminal = $^ GATerminal
gebMinimalObjectToExp (Product r r') =
  GAProduct $* [gebMinimalObjectToExp r, gebMinimalObjectToExp r']
gebMinimalObjectToExp (Coproduct r r') =
  GACoproduct $* [gebMinimalObjectToExp r, gebMinimalObjectToExp r']
gebMinimalObjectToExp ObjectExpression = $^ GAObjectExpression
gebMinimalObjectToExp (MorphismExpression domain codomain) =
  GAMorphismExpression $*
    [gebMinimalObjectToExp domain, gebMinimalObjectToExp codomain]

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
gebExpToMinimalObject (GAObjectExpression $* []) = Just ObjectExpression
gebExpToMinimalObject (GAMorphismExpression $* [domainRep, codomainRep]) =
  case (gebExpToMinimalObject domainRep, gebExpToMinimalObject codomainRep) of
    (Just domain, Just codomain) => Just $ MorphismExpression domain codomain
    _ => Nothing
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
gebMinimalObjectRepresentationComplete ObjectExpression = Refl
gebMinimalObjectRepresentationComplete (MorphismExpression r r') =
  rewrite gebMinimalObjectRepresentationComplete r in
  rewrite gebMinimalObjectRepresentationComplete r' in
  Refl

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

public export
Eq MinimalObject using decEqToEq where
  (==) = (==)

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
    ExpressionIntro : MinimalObject -> MinimalMorphism
    ExpressionElim : (exp, exp', eqCase, neqCase : MinimalMorphism) ->
      {auto expDomainsMatch :
        (minimalMorphismDomain exp) = (minimalMorphismDomain exp')} ->
      {auto expCodomainIsExpression :
        (minimalMorphismCodomain exp) = ObjectExpression} ->
      {auto expCodomainsMatch :
        (minimalMorphismCodomain exp) = (minimalMorphismCodomain exp')} ->
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
  minimalMorphismCodomain (ExpressionIntro _) = ObjectExpression
  minimalMorphismCodomain (ExpressionElim _ _ eqCase _) =
    minimalMorphismCodomain eqCase

mutual
  public export
  gebMinimalExpressionToExp : MinimalExpression -> GebSExp
  gebMinimalExpressionToExp (MinimalObjectExp o) = gebMinimalObjectToExp o
  gebMinimalExpressionToExp (MinimalMorphismExp m) = gebMinimalMorphismToExp m

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
  gebMinimalMorphismToExp (ProductIntro f g) =
    GAProductIntro $* [gebMinimalMorphismToExp f, gebMinimalMorphismToExp g]
  gebMinimalMorphismToExp (ProductElimLeft a b) =
    GAProductElimLeft $* [gebMinimalObjectToExp a, gebMinimalObjectToExp b]
  gebMinimalMorphismToExp (ProductElimRight a b) =
    GAProductElimRight $* [gebMinimalObjectToExp a, gebMinimalObjectToExp b]
  gebMinimalMorphismToExp (CoproductElim f g) =
    GACoproductElim $* [gebMinimalMorphismToExp f, gebMinimalMorphismToExp g]
  gebMinimalMorphismToExp (CoproductIntroLeft a b) =
    GACoproductIntroLeft $* [gebMinimalObjectToExp a, gebMinimalObjectToExp b]
  gebMinimalMorphismToExp (CoproductIntroRight a b) =
    GACoproductIntroRight $* [gebMinimalObjectToExp a, gebMinimalObjectToExp b]
  gebMinimalMorphismToExp (ExpressionIntro x) =
    GAExpressionIntro $* [gebMinimalObjectToExp x]
  gebMinimalMorphismToExp (ExpressionElim exp exp' eqCase neqCase) =
    GAExpressionElim $*
      [gebMinimalMorphismToExp exp,
       gebMinimalMorphismToExp exp',
       gebMinimalMorphismToExp eqCase,
       gebMinimalMorphismToExp neqCase]

public export
gebMorphismExpIsNotObject : (m : MinimalMorphism) ->
  gebExpToMinimalObject (gebMinimalMorphismToExp m) = Nothing
gebMorphismExpIsNotObject (Identity _) = Refl
gebMorphismExpIsNotObject (Compose _ _) = Refl
gebMorphismExpIsNotObject (FromInitial _) = Refl
gebMorphismExpIsNotObject (ToTerminal _) = Refl
gebMorphismExpIsNotObject (ProductIntro _ _) = Refl
gebMorphismExpIsNotObject (ProductElimLeft _ _) = Refl
gebMorphismExpIsNotObject (ProductElimRight _ _) = Refl
gebMorphismExpIsNotObject (CoproductElim _ _) = Refl
gebMorphismExpIsNotObject (CoproductIntroLeft _ _) = Refl
gebMorphismExpIsNotObject (CoproductIntroRight _ _) = Refl
gebMorphismExpIsNotObject (ExpressionIntro _) = Refl
gebMorphismExpIsNotObject (ExpressionElim _ _ _ _) = Refl

mutual
  public export
  gebExpToMinimalExp : GebSExp -> Maybe MinimalExpression
  gebExpToMinimalExp x with (gebExpToMinimalObject x, gebExpToMinimalMorphism x)
    proof p
      gebExpToMinimalExp x | (Just o, Just m) =
        let pfst = PairFstEq p in
        let psnd = PairSndEq p in
        void (gebExpIsNotBothObjectAndMorphism x o m pfst psnd)
      gebExpToMinimalExp x | (Just o, Nothing) = Just $ MinimalObjectExp o
      gebExpToMinimalExp x | (Nothing, Just m) = Just $ MinimalMorphismExp m
      gebExpToMinimalExp x | (Nothing, Nothing) = Nothing

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
  gebExpToMinimalMorphism (GAProductIntro $* [fExp, gExp]) =
    case (gebExpToMinimalMorphism fExp, gebExpToMinimalMorphism gExp) of
      (Just f, Just g) =>
        case (minimalObjectDecEq
          (minimalMorphismDomain f) (minimalMorphismDomain g)) of
            Yes domainsMatch => Just $ ProductIntro f g {domainsMatch}
            No _ => Nothing
      _ => Nothing
  gebExpToMinimalMorphism (GAProductElimLeft $* [aExp, bExp]) =
    case (gebExpToMinimalObject aExp, gebExpToMinimalObject bExp) of
      (Just a, Just b) => Just $ ProductElimLeft a b
      _ => Nothing
  gebExpToMinimalMorphism (GAProductElimRight $* [aExp, bExp]) =
    case (gebExpToMinimalObject aExp, gebExpToMinimalObject bExp) of
      (Just a, Just b) => Just $ ProductElimRight a b
      _ => Nothing
  gebExpToMinimalMorphism (GACoproductElim $* [fExp, gExp]) =
    case (gebExpToMinimalMorphism fExp, gebExpToMinimalMorphism gExp) of
      (Just f, Just g) =>
        case (minimalObjectDecEq
          (minimalMorphismCodomain f) (minimalMorphismCodomain g)) of
            Yes codomainsMatch => Just $ CoproductElim f g {codomainsMatch}
            No _ => Nothing
      _ => Nothing
  gebExpToMinimalMorphism (GACoproductIntroLeft $* [aExp, bExp]) =
    case (gebExpToMinimalObject aExp, gebExpToMinimalObject bExp) of
      (Just a, Just b) => Just $ CoproductIntroLeft a b
      _ => Nothing
  gebExpToMinimalMorphism (GACoproductIntroRight $* [aExp, bExp]) =
    case (gebExpToMinimalObject aExp, gebExpToMinimalObject bExp) of
      (Just a, Just b) => Just $ CoproductIntroRight a b
      _ => Nothing
  gebExpToMinimalMorphism (GAExpressionIntro $* [x]) =
    case gebExpToMinimalObject x of
      Just minimalObj => Just $ ExpressionIntro minimalObj
      _ => Nothing
  gebExpToMinimalMorphism (GAExpressionElim $* [exp, exp', eqExp, neqExp]) =
    case (gebExpToMinimalMorphism exp, gebExpToMinimalMorphism exp',
          gebExpToMinimalMorphism eqExp, gebExpToMinimalMorphism neqExp) of
      (Just exp, Just exp', Just eqCase, Just neqCase) =>
        case
          (minimalObjectDecEq
            (minimalMorphismDomain exp) (minimalMorphismDomain exp'),
           minimalObjectDecEq (minimalMorphismCodomain exp) ObjectExpression,
           minimalObjectDecEq
            (minimalMorphismCodomain exp) (minimalMorphismCodomain exp')) of
              (Yes domainsMatch, Yes expCodomainIsExpression,
              Yes expCodomainsMatch) =>
                case
                  (minimalObjectDecEq
                    (minimalMorphismDomain exp)
                    (minimalMorphismDomain eqCase),
                  minimalObjectDecEq
                    (minimalMorphismDomain exp)
                    (minimalMorphismDomain neqCase),
                  minimalObjectDecEq
                    (minimalMorphismCodomain eqCase)
                    (minimalMorphismCodomain neqCase)) of
                (Yes eqDomainsMatch, Yes neqDomainsMatch, Yes codomainsMatch) =>
                  Just $ ExpressionElim exp exp' eqCase neqCase
                _ => Nothing
              _ => Nothing
      _ => Nothing
  gebExpToMinimalMorphism _ = Nothing

  public export
  gebExpIsNotBothObjectAndMorphism : (x : GebSExp) ->
    (o : MinimalObject) -> (m : MinimalMorphism) ->
    gebExpToMinimalObject x = Just o -> gebExpToMinimalMorphism x = Just m ->
    Void
  gebExpIsNotBothObjectAndMorphism (GALanguageRefinement $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMinimal $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAObject $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAInitial $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GATerminal $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProduct $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproduct $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAObjectExpression $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMorphismExpression $* _) _ _ eqo eqm =
    case eqm of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMorphism $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GATerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAUnitTerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAExFalsoTerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAMorphismTerm $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAApplication $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAFromInitial $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAToTerminal $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAIdentity $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACompose $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProductIntro $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProductElimLeft $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAProductElimRight $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproductElim $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproductIntroLeft $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GACoproductIntroRight $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAExpressionIntro $* _) _ _ eqo eqm =
    case eqo of Refl impossible
  gebExpIsNotBothObjectAndMorphism (GAExpressionElim $* _) _ _ eqo eqm =
    case eqo of Refl impossible

public export
gebObjectExpIsNotMorphism : (o : MinimalObject) ->
  gebExpToMinimalMorphism (gebMinimalObjectToExp o) = Nothing
gebObjectExpIsNotMorphism Initial = Refl
gebObjectExpIsNotMorphism Terminal = Refl
gebObjectExpIsNotMorphism (Product _ _) = Refl
gebObjectExpIsNotMorphism (Coproduct _ _) = Refl
gebObjectExpIsNotMorphism ObjectExpression = Refl
gebObjectExpIsNotMorphism (MorphismExpression _ _) = Refl

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
gebMinimalMorphismRepresentationComplete (ProductIntro f g {domainsMatch}) =
  rewrite gebMinimalMorphismRepresentationComplete f in
  rewrite gebMinimalMorphismRepresentationComplete g in
  rewrite domainsMatch in
  rewrite decEqRefl minimalObjectDecEq (minimalMorphismDomain g) in
  rewrite uip domainsMatch _ in
  Refl
gebMinimalMorphismRepresentationComplete (ProductElimLeft a b) =
  rewrite gebMinimalObjectRepresentationComplete a in
  rewrite gebMinimalObjectRepresentationComplete b in
  Refl
gebMinimalMorphismRepresentationComplete (ProductElimRight a b) =
  rewrite gebMinimalObjectRepresentationComplete a in
  rewrite gebMinimalObjectRepresentationComplete b in
  Refl
gebMinimalMorphismRepresentationComplete (CoproductElim f g {codomainsMatch}) =
  rewrite gebMinimalMorphismRepresentationComplete f in
  rewrite gebMinimalMorphismRepresentationComplete g in
  rewrite codomainsMatch in
  rewrite decEqRefl minimalObjectDecEq (minimalMorphismCodomain g) in
  rewrite uip codomainsMatch _ in
  Refl
gebMinimalMorphismRepresentationComplete (CoproductIntroLeft a b) =
  rewrite gebMinimalObjectRepresentationComplete a in
  rewrite gebMinimalObjectRepresentationComplete b in
  Refl
gebMinimalMorphismRepresentationComplete (CoproductIntroRight a b) =
  rewrite gebMinimalObjectRepresentationComplete a in
  rewrite gebMinimalObjectRepresentationComplete b in
  Refl
gebMinimalMorphismRepresentationComplete (ExpressionIntro o) =
  rewrite gebMinimalObjectRepresentationComplete o in
  Refl
gebMinimalMorphismRepresentationComplete
  (ExpressionElim exp exp' eqCase neqCase
    {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
    {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) =
      rewrite gebMinimalMorphismRepresentationComplete exp in
      rewrite gebMinimalMorphismRepresentationComplete exp' in
      rewrite gebMinimalMorphismRepresentationComplete eqCase in
      rewrite gebMinimalMorphismRepresentationComplete neqCase in
      rewrite sym expDomainsMatch in
      rewrite sym expCodomainIsExpression in
      rewrite expCodomainsMatch in
      rewrite decEqRefl minimalObjectDecEq (minimalMorphismDomain exp) in
      rewrite decEqRefl minimalObjectDecEq (minimalMorphismCodomain exp') in
      rewrite sym eqDomainMatches in
      rewrite decEqRefl minimalObjectDecEq (minimalMorphismDomain exp) in
      rewrite sym neqDomainMatches in
      rewrite decEqRefl minimalObjectDecEq (minimalMorphismDomain exp) in
      rewrite sym eqCodomainsMatch in
      rewrite decEqRefl minimalObjectDecEq (minimalMorphismCodomain eqCase) in
      rewrite uip eqCodomainsMatch _ in
      rewrite uip neqDomainMatches _ in
      rewrite uip eqDomainMatches _ in
      rewrite uip expCodomainsMatch _ in
      rewrite uip expCodomainIsExpression _ in
      rewrite uip expDomainsMatch _ in
      Refl

export
minimalMorphismDecEq : DecEqPred MinimalMorphism
minimalMorphismDecEq =
  encodingDecEq
    gebMinimalMorphismToExp
    gebExpToMinimalMorphism
    gebMinimalMorphismRepresentationComplete
    decEq

public export
gebMinimalExpRepresentationComplete : (r : MinimalExpression) ->
  gebExpToMinimalExp (gebMinimalExpressionToExp r) = Just r
gebMinimalExpRepresentationComplete (MinimalObjectExp o) =
  rewrite gebObjectExpIsNotMorphism o in
  rewrite gebMinimalObjectRepresentationComplete o in
  Refl
gebMinimalExpRepresentationComplete (MinimalMorphismExp m) =
  rewrite gebMorphismExpIsNotObject m in
  rewrite gebMinimalMorphismRepresentationComplete m in
  Refl

public export
DecEq MinimalMorphism where
  decEq = minimalMorphismDecEq

public export
Eq MinimalMorphism using decEqToEq where
  (==) = (==)

public export
Show MinimalMorphism where
  show m = show (gebMinimalMorphismToExp m)

public export
minimalExpressionDecEq : DecEqPred MinimalExpression
minimalExpressionDecEq (MinimalObjectExp x) (MinimalObjectExp x') =
  case decEq x x' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
minimalExpressionDecEq (MinimalObjectExp x) (MinimalMorphismExp x') =
  No $ \eq => case eq of Refl impossible
minimalExpressionDecEq (MinimalMorphismExp x) (MinimalObjectExp x') =
  No $ \eq => case eq of Refl impossible
minimalExpressionDecEq (MinimalMorphismExp x) (MinimalMorphismExp x') =
  case decEq x x' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq MinimalExpression where
  decEq = minimalExpressionDecEq

public export
Eq MinimalExpression using decEqToEq where
  (==) = (==)

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
interpretMinimalObject ObjectExpression = MinimalObject
interpretMinimalObject (MorphismExpression domain codomain) =
  (m : MinimalMorphism **
   (minimalMorphismDomain m = domain, minimalMorphismCodomain m = codomain))

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
interpretMinimalMorphism (ProductIntro f g {domainsMatch}) x =
  (interpretMinimalMorphism f x,
   interpretMinimalMorphism g (rewrite sym domainsMatch in x))
interpretMinimalMorphism (ProductElimLeft a b) x = fst x
interpretMinimalMorphism (ProductElimRight a b) x = snd x
interpretMinimalMorphism (CoproductElim f g {codomainsMatch}) x =
  case x of
    Left x' => interpretMinimalMorphism f x'
    Right x' => rewrite codomainsMatch in interpretMinimalMorphism g x'
interpretMinimalMorphism (CoproductIntroLeft a b) x = Left x
interpretMinimalMorphism (CoproductIntroRight a b) x = Right x
interpretMinimalMorphism (ExpressionIntro exp) () = exp
interpretMinimalMorphism (ExpressionElim exp exp' eqCase neqCase
  {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
  {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) x =
    let
      y = interpretMinimalMorphism exp x
      y' = replace {p=interpretMinimalObject} expCodomainIsExpression y
      z = interpretMinimalMorphism exp' (rewrite sym expDomainsMatch in x)
      z' = replace {p=interpretMinimalObject} (sym expCodomainsMatch) z
      z'' = replace {p=interpretMinimalObject} expCodomainIsExpression z'
    in
    if y' == z'' then
      interpretMinimalMorphism eqCase (rewrite sym eqDomainMatches in x)
    else
      rewrite eqCodomainsMatch in
      interpretMinimalMorphism neqCase (rewrite sym neqDomainMatches in x)

-----------------------------------
---- Correctness of reflection ----
-----------------------------------

public export
minimalObjectQuote : MinimalObject -> interpretMinimalObject ObjectExpression
minimalObjectQuote = Prelude.id

public export
minimalObjectUnquote : interpretMinimalObject ObjectExpression -> MinimalObject
minimalObjectUnquote = Prelude.id

export
minimalObjectUnquoteQuoteCorrect : (r : MinimalObject) ->
  minimalObjectUnquote (minimalObjectQuote r) = r
minimalObjectUnquoteQuoteCorrect r = Refl

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

public export
data MinimalTerm : (numApplications : Nat) -> MinimalTermType -> Type where
  UnappliedMorphismTerm : (morphism : MinimalMorphism) ->
    MinimalTerm 0 $
      MinimalMorphismTerm
        (minimalMorphismDomain morphism)
        (minimalMorphismCodomain morphism)
  Application : {morphismApplications, termApplications : Nat} ->
    {domain, codomain : MinimalObject} ->
    MinimalTerm morphismApplications (MinimalMorphismTerm domain codomain) ->
    MinimalTerm termApplications (MinimalTypeTerm domain) ->
    MinimalTerm
      (S $ morphismApplications + termApplications) (MinimalTypeTerm codomain)
  ExFalsoTerm : {numApplications : Nat} -> {type : MinimalObject} ->
    MinimalTerm numApplications (MinimalTypeTerm Initial) ->
    MinimalTerm numApplications $ MinimalTypeTerm type
  UnitTerm : MinimalTerm 0 $ MinimalTypeTerm Terminal
  PairTerm : {leftApplications, rightApplications : Nat} ->
    {left, right : MinimalObject} ->
    MinimalTerm leftApplications (MinimalTypeTerm left) ->
    MinimalTerm rightApplications (MinimalTypeTerm right) ->
    MinimalTerm (leftApplications + rightApplications) $
      MinimalTypeTerm $ Product left right
  MinimalLeft :
    {leftApplications : Nat} -> {left : MinimalObject} ->
    MinimalTerm leftApplications (MinimalTypeTerm left) ->
    (right : MinimalObject) ->
    MinimalTerm leftApplications $ MinimalTypeTerm $ Coproduct left right
  MinimalRight :
    (left : MinimalObject) ->
    {rightApplications : Nat} -> {right : MinimalObject} ->
    MinimalTerm rightApplications (MinimalTypeTerm right) ->
    MinimalTerm rightApplications $ MinimalTypeTerm $ Coproduct left right
  ExpressionTerm : MinimalObject ->
    MinimalTerm 0 $ MinimalTypeTerm $ ObjectExpression

public export
MinimalFullyAppliedTerm : MinimalTermType -> Type
MinimalFullyAppliedTerm = MinimalTerm 0

public export
gebMinimalTermToExp : {type: MinimalTermType} -> {numApplications : Nat} ->
  MinimalTerm numApplications type -> GebSExp
gebMinimalTermToExp (Application f x) =
  GAApplication $* [gebMinimalTermToExp f, gebMinimalTermToExp x]
gebMinimalTermToExp (UnappliedMorphismTerm morphism) =
  GAMorphismTerm $* [gebMinimalMorphismToExp morphism]
gebMinimalTermToExp {type=(MinimalTypeTerm type)} (ExFalsoTerm ti) =
  GAExFalsoTerm $* [gebMinimalTermToExp ti, gebMinimalObjectToExp type]
gebMinimalTermToExp UnitTerm = $^ GAUnitTerm
gebMinimalTermToExp
  (PairTerm {leftApplications} {rightApplications} {left} {right}
   leftTerm rightTerm) =
    GAPairTerm $* [gebMinimalTermToExp leftTerm, gebMinimalTermToExp rightTerm]
gebMinimalTermToExp {numApplications} (MinimalLeft left right) =
  GALeftTerm $* [gebMinimalTermToExp left, gebMinimalObjectToExp right]
gebMinimalTermToExp {numApplications} (MinimalRight left right) =
  GARightTerm $* [gebMinimalObjectToExp left, gebMinimalTermToExp right]
gebMinimalTermToExp (ExpressionTerm x) =
  GAExpressionTerm $* [gebMinimalObjectToExp x]

public export
gebExpToMinimalTerm :
  GebSExp -> Maybe (type : MinimalTermType ** n : Nat ** MinimalTerm n type)
gebExpToMinimalTerm (GAMorphismTerm $* [x]) =
  case gebExpToMinimalMorphism x of
    Just morphism => Just
      (MinimalMorphismTerm
        (minimalMorphismDomain morphism)
        (minimalMorphismCodomain morphism) **
       0 **
       (UnappliedMorphismTerm morphism))
    Nothing => Nothing
gebExpToMinimalTerm (GAExFalsoTerm $* [ti, ty]) =
  case (gebExpToMinimalTerm ti, gebExpToMinimalObject ty) of
    (Just (MinimalTypeTerm Initial ** n ** initialTerm), Just type) =>
      Just (MinimalTypeTerm type ** n ** ExFalsoTerm initialTerm)
    _ => Nothing
gebExpToMinimalTerm (GAUnitTerm $* []) =
  Just (MinimalTypeTerm Terminal ** 0 ** UnitTerm)
gebExpToMinimalTerm (GAPairTerm $* [left, right]) with
  (gebExpToMinimalTerm left, gebExpToMinimalTerm right)
    gebExpToMinimalTerm (GAPairTerm $* [left, right]) |
      (Just (MinimalTypeTerm leftObject ** nLeft ** leftTerm),
       Just (MinimalTypeTerm rightObject ** nRight ** rightTerm)) =
        Just
          (MinimalTypeTerm (Product leftObject rightObject) **
           nLeft + nRight **
           (PairTerm leftTerm rightTerm))
    gebExpToMinimalTerm (GAPairTerm $* [left, right]) |
      _ = Nothing
gebExpToMinimalTerm (GAApplication $* [fExp, xExp]) =
  case (gebExpToMinimalTerm fExp, gebExpToMinimalTerm xExp) of
    (Just (fType ** nLeft ** f), Just (xType ** nRight ** x)) =>
      case fType of
        MinimalMorphismTerm domain codomain =>
          case xType of
            MinimalTypeTerm domain' => case decEq domain domain' of
              Yes Refl =>
                Just
                  (MinimalTypeTerm codomain **
                   S (nLeft + nRight) **
                   Application f x)
              No _ => Nothing
            _ => Nothing
        _ => Nothing
    _ => Nothing
gebExpToMinimalTerm (GAExpressionTerm $* [exp]) = gebExpToMinimalTerm exp
gebExpToMinimalTerm (GALeftTerm $* [leftExp, rightExp]) =
  case (gebExpToMinimalTerm leftExp, gebExpToMinimalObject rightExp) of
    (Just (MinimalTypeTerm leftObject ** nLeft ** leftTerm),
     Just rightObject) =>
      Just
        (MinimalTypeTerm (Coproduct leftObject rightObject) **
         nLeft **
         MinimalLeft leftTerm rightObject)
    _ => Nothing
gebExpToMinimalTerm (GARightTerm $* [leftExp, rightExp]) =
  case (gebExpToMinimalObject leftExp, gebExpToMinimalTerm rightExp) of
    (Just leftObject,
     Just (MinimalTypeTerm rightObject ** nRight ** rightTerm)) =>
      Just
        (MinimalTypeTerm (Coproduct leftObject rightObject) **
         nRight **
         MinimalRight leftObject rightTerm)
    _ => Nothing
gebExpToMinimalTerm _ = Nothing

public export
gebMinimalTermRepresentationComplete :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) ->
  gebExpToMinimalTerm
    (gebMinimalTermToExp {type} {numApplications} term) =
      Just (type ** numApplications ** term)
gebMinimalTermRepresentationComplete (Application {domain} f x) =
  rewrite gebMinimalTermRepresentationComplete f in
  rewrite gebMinimalTermRepresentationComplete x in
  rewrite decEqRefl minimalObjectDecEq domain in
  Refl
gebMinimalTermRepresentationComplete
  (UnappliedMorphismTerm morphism) =
    rewrite gebMinimalMorphismRepresentationComplete morphism in
    Refl
gebMinimalTermRepresentationComplete (ExFalsoTerm ti) =
  let tiComplete = gebMinimalTermRepresentationComplete ti in
  ?gebMinimalTermRepresentationComplete_hole_exfalso
gebMinimalTermRepresentationComplete UnitTerm =
  Refl
gebMinimalTermRepresentationComplete (PairTerm left right) =
  ?gebMinimalTermRepresentationComplete_hole_pair
gebMinimalTermRepresentationComplete
  (MinimalLeft left right) =
    ?gebMinimalTermRepresentationComplete_hole_left
gebMinimalTermRepresentationComplete
  (MinimalRight left right) =
    ?gebMinimalTermRepresentationComplete_hole_right
gebMinimalTermRepresentationComplete (ExpressionTerm x) =
  ?gebMinimalTermRepresentationComplete_hole_expression

public export
(type : MinimalTermType) => (n : Nat) => Show (MinimalTerm n type) where
  show term = show (gebMinimalTermToExp term)

public export
interpretMinimalTermType : MinimalTermType -> Type
interpretMinimalTermType (MinimalTypeTerm type) = interpretMinimalObject type
interpretMinimalTermType (MinimalMorphismTerm domain codomain) =
  interpretMinimalObject domain -> interpretMinimalObject codomain

public export
interpretMinimalTerm : {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) -> interpretMinimalTermType type
interpretMinimalTerm (Application f x) =
  interpretMinimalTerm f $ interpretMinimalTerm x
interpretMinimalTerm (UnappliedMorphismTerm morphism) =
  interpretMinimalMorphism morphism
interpretMinimalTerm (ExFalsoTerm v) = void $ interpretMinimalTerm v
interpretMinimalTerm UnitTerm = ()
interpretMinimalTerm (PairTerm left right) =
  (interpretMinimalTerm left, interpretMinimalTerm right)
interpretMinimalTerm (MinimalLeft left right) =
  Left $ interpretMinimalTerm left
interpretMinimalTerm (MinimalRight left right) =
  Right $ interpretMinimalTerm right
interpretMinimalTerm (ExpressionTerm x) = x

public export
gebNoExFalsoTerm : {numApplications : Nat} ->
  (ti : MinimalTerm numApplications (MinimalTypeTerm Initial)) ->
  Void
gebNoExFalsoTerm ti = void $ interpretMinimalTerm ti

-- | A correct morphism transformation preserves the interpretation of
-- | term application.
public export
correctMinimalMorphismTransformPreservesTermInterpretation :
  (transform : MinimalMorphismTransform) ->
  {domainTransformCorrect :
    MinimalMorphismTransformDomainCorrect transform} ->
  {codomainTransformCorrect :
    MinimalMorphismTransformCodomainCorrect transform} ->
  MinimalMorphismTransformCorrect
    transform domainTransformCorrect codomainTransformCorrect ->
  (m : MinimalMorphism) ->
  {numApplications : Nat} ->
  (term :
    MinimalTerm numApplications
      (MinimalTypeTerm (minimalMorphismDomain m))) ->
  (term' :
    MinimalTerm numApplications
      (MinimalTypeTerm (minimalMorphismDomain (transform m)))) ->
  interpretMinimalTerm term =
    (rewrite sym (domainTransformCorrect m) in (interpretMinimalTerm term')) ->
  interpretMinimalTerm
    (Application (UnappliedMorphismTerm m) term) =
  (rewrite sym (codomainTransformCorrect m) in (interpretMinimalTerm
    (Application (UnappliedMorphismTerm (transform m)) term')))
correctMinimalMorphismTransformPreservesTermInterpretation
  transform transformCorrect m {numApplications} term term' termEq =
    ?correctMinimalMorphismTransformPreservesTermInterpretation_hole

public export
bigStepMinimalMorphismReduction :
  (m : MinimalMorphism) ->
  MinimalFullyAppliedTerm (MinimalTypeTerm (minimalMorphismDomain m)) ->
  MinimalFullyAppliedTerm (MinimalTypeTerm (minimalMorphismCodomain m))
bigStepMinimalMorphismReduction (Identity _) x = x
bigStepMinimalMorphismReduction (Compose g f {composable}) x =
  bigStepMinimalMorphismReduction g $
    rewrite sym composable in (bigStepMinimalMorphismReduction f x)
bigStepMinimalMorphismReduction (FromInitial _) x = ExFalsoTerm x
bigStepMinimalMorphismReduction (ToTerminal y) x = UnitTerm
bigStepMinimalMorphismReduction (ProductIntro f g {domainsMatch}) x =
  PairTerm
    (bigStepMinimalMorphismReduction f x)
    (bigStepMinimalMorphismReduction g $ rewrite sym domainsMatch in x)
bigStepMinimalMorphismReduction (ProductElimLeft a b) x = case x of
  PairTerm {leftApplications=0} {rightApplications=0} left right => left
  ExFalsoTerm ti => ExFalsoTerm ti
bigStepMinimalMorphismReduction (ProductElimRight a b) x = case x of
  PairTerm {leftApplications=0} {rightApplications=0} left right => right
  ExFalsoTerm ti => ExFalsoTerm ti
bigStepMinimalMorphismReduction (CoproductElim f g {codomainsMatch}) x =
  case x of
    MinimalLeft left _ =>
      bigStepMinimalMorphismReduction f left
    MinimalRight _ right =>
      rewrite codomainsMatch in bigStepMinimalMorphismReduction g right
    ExFalsoTerm ti => ExFalsoTerm ti
bigStepMinimalMorphismReduction (CoproductIntroLeft left right) x =
  MinimalLeft x right
bigStepMinimalMorphismReduction (CoproductIntroRight left right) x =
  MinimalRight left x
bigStepMinimalMorphismReduction (ExpressionIntro exp) _ = ExpressionTerm exp
bigStepMinimalMorphismReduction (ExpressionElim exp exp' eqCase neqCase
  {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
  {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) x =
    let
      xReduced = bigStepMinimalMorphismReduction exp x
      xReduced' = bigStepMinimalMorphismReduction exp'
        (rewrite sym expDomainsMatch in x)
      xReducedRewritten =
        replace {p=(MinimalTerm 0 . MinimalTypeTerm)}
          expCodomainIsExpression xReduced
      xReducedRewritten' =
        replace {p=(MinimalTerm 0 . MinimalTypeTerm)}
          expCodomainIsExpression (rewrite expCodomainsMatch in xReduced')
      xInterpreted = interpretMinimalTerm xReducedRewritten
      xInterpreted' = interpretMinimalTerm xReducedRewritten'
      eqCaseReduced =
        bigStepMinimalMorphismReduction
          eqCase (rewrite sym eqDomainMatches in x)
      eqCaseReduced' =
        bigStepMinimalMorphismReduction
          neqCase (rewrite sym neqDomainMatches in x)
    in
    if xInterpreted == xInterpreted' then
      eqCaseReduced else
    (replace {p=(MinimalTerm 0. MinimalTypeTerm)}
      (sym eqCodomainsMatch) eqCaseReduced')

public export
bigStepMinimalTermReduction :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  MinimalTerm numApplications type ->
  MinimalFullyAppliedTerm type
bigStepMinimalTermReduction (Application f x) with
  (bigStepMinimalTermReduction f, bigStepMinimalTermReduction x)
    bigStepMinimalTermReduction (Application f x) |
      (UnappliedMorphismTerm m, xReduced) =
        bigStepMinimalMorphismReduction m xReduced
bigStepMinimalTermReduction (UnappliedMorphismTerm m) = UnappliedMorphismTerm m
bigStepMinimalTermReduction (ExFalsoTerm ti) =
  ExFalsoTerm $ bigStepMinimalTermReduction ti
bigStepMinimalTermReduction UnitTerm = UnitTerm
bigStepMinimalTermReduction (PairTerm left right) =
  PairTerm
    (bigStepMinimalTermReduction left)
    (bigStepMinimalTermReduction right)
bigStepMinimalTermReduction (MinimalLeft left right) =
  MinimalLeft (bigStepMinimalTermReduction left) right
bigStepMinimalTermReduction (MinimalRight left right) =
  MinimalRight left (bigStepMinimalTermReduction right)
bigStepMinimalTermReduction (ExpressionTerm x) = ExpressionTerm x

mutual
  public export
  bigStepMinimalMorphismReductionCorrect :
    (m : MinimalMorphism) ->
    (x : MinimalFullyAppliedTerm (MinimalTypeTerm (minimalMorphismDomain m))) ->
    interpretMinimalTerm (bigStepMinimalMorphismReduction m x) =
      interpretMinimalTerm (UnappliedMorphismTerm m) (interpretMinimalTerm x)
  bigStepMinimalMorphismReductionCorrect m x =
    ?bigStepMinimalMorphismReductionCorrect_hole

  public export
  bigStepMinimalTermReductionCorrect :
    {type : MinimalTermType} -> {numApplications : Nat} ->
    (term : MinimalTerm numApplications type) ->
    interpretMinimalTerm (bigStepMinimalTermReduction term) =
      interpretMinimalTerm term
  bigStepMinimalTermReductionCorrect {type} term =
    ?bigStepMinimalTermReductionCorrect_hole

public export
smallStepMinimalMorphismReduction :
  (m : MinimalMorphism) ->
  {numApplications : Nat} ->
  MinimalTerm numApplications (MinimalTypeTerm (minimalMorphismDomain m)) ->
  (remainingApplications : Nat **
   MinimalTerm
    remainingApplications (MinimalTypeTerm (minimalMorphismCodomain m)))
smallStepMinimalMorphismReduction (Identity x) term =
  ?smallStepMinimalMorphismReduction_hole_ident
smallStepMinimalMorphismReduction (Compose g f) term =
  ?smallStepMinimalMorphismReduction_hole_compose
smallStepMinimalMorphismReduction (FromInitial x) term =
  ?smallStepMinimalMorphismReduction_hole_frominit
smallStepMinimalMorphismReduction (ToTerminal x) term =
  ?smallStepMinimalMorphismReduction_hole_toterm
smallStepMinimalMorphismReduction (ProductIntro f g) term =
  ?smallStepMinimalMorphismReduction_hole_prodintro
smallStepMinimalMorphismReduction (ProductElimLeft a b) term =
  ?smallStepMinimalMorphismReduction_hole_prodleft
smallStepMinimalMorphismReduction (ProductElimRight a b) term =
  ?smallStepMinimalMorphismReduction_hole_prodright
smallStepMinimalMorphismReduction (CoproductElim f g) term =
  ?smallStepMinimalMorphismReduction_hole_coelim
smallStepMinimalMorphismReduction (CoproductIntroLeft a b) term =
  ?smallStepMinimalMorphismReduction_hole_cointroleft
smallStepMinimalMorphismReduction (CoproductIntroRight a b) term =
  ?smallStepMinimalMorphismReduction_hole_cointroright
smallStepMinimalMorphismReduction (ExpressionIntro x) term =
  ?smallStepMinimalMorphismReduction_hole_expIntro
smallStepMinimalMorphismReduction
  (ExpressionElim exp exp' eqCase neqCase) term =
    ?smallStepMinimalMorphismReduction_hole_expElim

public export
smallStepMinimalTermReduction :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  MinimalTerm numApplications type ->
  (remainingApplications : Nat ** MinimalTerm remainingApplications type)
smallStepMinimalTermReduction (UnappliedMorphismTerm morphism) =
  ?smallStepMinimalTermReduction_hole_unapplied
smallStepMinimalTermReduction (Application x y) =
  ?smallStepMinimalTermReduction_hole_app
smallStepMinimalTermReduction (ExFalsoTerm ti) =
  ?smallStepMinimalTermReduction_hole_exfalso
smallStepMinimalTermReduction UnitTerm =
  ?smallStepMinimalTermReduction_hole_unit
smallStepMinimalTermReduction (PairTerm x y) =
  ?smallStepMinimalTermReduction_hole_pair
smallStepMinimalTermReduction (MinimalLeft x right) =
  ?smallStepMinimalTermReduction_hole_left
smallStepMinimalTermReduction (MinimalRight left x) =
  ?smallStepMinimalTermReduction_hole_right
smallStepMinimalTermReduction (ExpressionTerm x) =
  ?smallStepMinimalTermReduction_hole_exp

public export
data SmallStepMinimalTermReductionCompletes :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) ->
  (reduced : MinimalFullyAppliedTerm type) -> Type
  where
    SmallStepMinimalReductionLastStep :
      {type : MinimalTermType} -> {numApplications : Nat} ->
      {term : MinimalTerm numApplications type} ->
      {reduced : MinimalFullyAppliedTerm type} ->
      smallStepMinimalTermReduction term = Left reduced ->
      SmallStepMinimalTermReductionCompletes term reduced
    SmallStepMinimalReductionPreviousStep :
      {type : MinimalTermType} ->
      {numApplications, intermediateNumApplications : Nat} ->
      {term : MinimalTerm numApplications type} ->
      {intermediateTerm : MinimalTerm intermediateNumApplications type} ->
      {reduced : MinimalFullyAppliedTerm type} ->
      smallStepMinimalTermReduction term = Right intermediateTerm ->
      SmallStepMinimalTermReductionCompletes intermediateTerm reduced ->
      SmallStepMinimalTermReductionCompletes term reduced

public export
smallStepMinimalTermReductionCompletes :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) ->
  DPair
    (MinimalFullyAppliedTerm type)
    (SmallStepMinimalTermReductionCompletes term)
smallStepMinimalTermReductionCompletes {type} term =
  ?smallStepMinimalTermReductionCompletes_hole

public export
smallStepMinimalTermReductionCorrect :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) ->
  interpretMinimalTerm
    (fst (smallStepMinimalTermReductionCompletes term)) =
      interpretMinimalTerm term
smallStepMinimalTermReductionCorrect {type} term =
  ?smallStepMinimalTermReductionCorrect_hole

public export
minimalTermReductionsConsistent :
  {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) ->
  bigStepMinimalTermReduction term =
    snd (smallStepMinimalTermReductionCompletes term)
minimalTermReductionsConsistent term = ?minimalTermReductionsConsistent_hole
-}
