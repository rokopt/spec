module Geb.GebSExp

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.SExp

%default total

public export
data GebAtom : Type where
  -- | The notion of a language itself.
  GALanguage : GebAtom

  -- | The minimal programming language, with substitution (pattern-matching)
  -- | only.
  GAMinimal : GebAtom

  -- | A language with fixed points of substitution.
  GAHigherOrderInductive : GebAtom

  -- | The notion of an object of any programming language.
  GAObject : GebAtom

  -- | Objects common to all programming languages.
  GAPromoteObject : GebAtom
  GAAtom : GebAtom
  GASExp : GebAtom
  GASList : GebAtom

  -- | The notion of a morphism of any programming language.
  GAMorphism : GebAtom

  -- | Morphisms common to all programming languages.
  GAPromoteMorphism : GebAtom
  GAIdentity : GebAtom
  GACompose : GebAtom
  GAAtomIntro : GebAtom
  GAAtomElim : GebAtom
  GASExpIntro : GebAtom
  GASExpElim : GebAtom
  GASListIntroNil : GebAtom
  GASListIntroCons : GebAtom
  GASListElim : GebAtom

  -- | The notion of a term of any programming language.
  GATerm : GebAtom

  -- | Terms common to all programming languages.
  GAAtomTerm : GebAtom
  GASExpTerm : GebAtom
  GASListTerm : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GALanguage = 0
gaEncode GAMinimal = 1
gaEncode GAHigherOrderInductive = 2
gaEncode GAObject = 3
gaEncode GAPromoteObject = 4
gaEncode GAAtom = 5
gaEncode GASExp = 6
gaEncode GASList = 7
gaEncode GAMorphism = 8
gaEncode GAPromoteMorphism = 9
gaEncode GAIdentity = 10
gaEncode GACompose = 11
gaEncode GAAtomIntro = 12
gaEncode GAAtomElim = 13
gaEncode GASExpIntro = 14
gaEncode GASExpElim = 15
gaEncode GASListIntroNil = 16
gaEncode GASListIntroCons = 17
gaEncode GASListElim = 18
gaEncode GATerm = 19
gaEncode GAAtomTerm = 20
gaEncode GASExpTerm = 21
gaEncode GASListTerm = 22

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GALanguage
gaDecode 1 = Just GAMinimal
gaDecode 2 = Just GAHigherOrderInductive
gaDecode 3 = Just GAObject
gaDecode 4 = Just GAPromoteObject
gaDecode 5 = Just GAAtom
gaDecode 6 = Just GASExp
gaDecode 7 = Just GASList
gaDecode 8 = Just GAMorphism
gaDecode 9 = Just GAPromoteMorphism
gaDecode 10 = Just GAIdentity
gaDecode 11 = Just GACompose
gaDecode 12 = Just GAAtomIntro
gaDecode 13 = Just GAAtomElim
gaDecode 14 = Just GASExpIntro
gaDecode 15 = Just GASExpElim
gaDecode 16 = Just GASListIntroNil
gaDecode 17 = Just GASListIntroCons
gaDecode 18 = Just GASListElim
gaDecode 19 = Just GATerm
gaDecode 20 = Just GAAtomTerm
gaDecode 21 = Just GASExpTerm
gaDecode 22 = Just GASListTerm
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GALanguage = Refl
gaDecodeEncodeIsJust GAMinimal = Refl
gaDecodeEncodeIsJust GAHigherOrderInductive = Refl
gaDecodeEncodeIsJust GAObject = Refl
gaDecodeEncodeIsJust GAPromoteObject = Refl
gaDecodeEncodeIsJust GAAtom = Refl
gaDecodeEncodeIsJust GASExp = Refl
gaDecodeEncodeIsJust GASList = Refl
gaDecodeEncodeIsJust GAMorphism = Refl
gaDecodeEncodeIsJust GAPromoteMorphism = Refl
gaDecodeEncodeIsJust GAIdentity = Refl
gaDecodeEncodeIsJust GACompose = Refl
gaDecodeEncodeIsJust GAAtomIntro = Refl
gaDecodeEncodeIsJust GAAtomElim = Refl
gaDecodeEncodeIsJust GASExpIntro = Refl
gaDecodeEncodeIsJust GASExpElim = Refl
gaDecodeEncodeIsJust GASListIntroNil = Refl
gaDecodeEncodeIsJust GASListIntroCons = Refl
gaDecodeEncodeIsJust GASListElim = Refl
gaDecodeEncodeIsJust GATerm = Refl
gaDecodeEncodeIsJust GAAtomTerm = Refl
gaDecodeEncodeIsJust GASExpTerm = Refl
gaDecodeEncodeIsJust GASListTerm = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GALanguage = "Language"
gebAtomToString GAMinimal = "Minimal"
gebAtomToString GAHigherOrderInductive = "HigherOrderInductive"
gebAtomToString GAObject = "Object"
gebAtomToString GAPromoteObject = "PromoteObject"
gebAtomToString GAAtom = "Atom"
gebAtomToString GASExp = "SExp"
gebAtomToString GASList = "SList"
gebAtomToString GAMorphism = "Morphism"
gebAtomToString GAPromoteMorphism = "PromoteMorphism"
gebAtomToString GAIdentity = "Identity"
gebAtomToString GACompose = "Compose"
gebAtomToString GAAtomIntro = "AtomIntro"
gebAtomToString GAAtomElim = "AtomElim"
gebAtomToString GASExpIntro = "SExpIntro"
gebAtomToString GASExpElim = "SExpElim"
gebAtomToString GASListIntroNil = "SListIntroNil"
gebAtomToString GASListIntroCons = "SListIntroCons"
gebAtomToString GASListElim = "SListElim"
gebAtomToString GATerm = "Term"
gebAtomToString GAAtomTerm = "AtomTerm"
gebAtomToString GASExpTerm = "SExpTerm"
gebAtomToString GASListTerm = "SListTerm"

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
  Minimal : Language
  HigherOrderInductive : Language

public export
gebLanguageToExp : Language -> GebSExp
gebLanguageToExp Minimal = $^ GAMinimal
gebLanguageToExp HigherOrderInductive = $^ GAHigherOrderInductive

public export
gebExpToLanguage : GebSExp -> Maybe Language
gebExpToLanguage (GAMinimal $* []) = Just Minimal
gebExpToLanguage (GAHigherOrderInductive $* []) = Just HigherOrderInductive
gebExpToLanguage _ = Nothing

public export
gebLanguageRepresentationComplete : (r : Language) ->
  gebExpToLanguage (gebLanguageToExp r) = Just r
gebLanguageRepresentationComplete Minimal = Refl
gebLanguageRepresentationComplete HigherOrderInductive = Refl

export
languageDecEq : DecEqPred Language
languageDecEq =
  encodingDecEq
    gebLanguageToExp
    gebExpToLanguage
    gebLanguageRepresentationComplete
    decEq

public export
DecEq Language where
  decEq = languageDecEq

public export
Eq Language using decEqToEq where
  (==) = (==)

public export
Show Language where
  show l = show (gebLanguageToExp l)

------------------------------------------------------------------
---- Objects of reflective (SExp-based) programming languages ----
------------------------------------------------------------------

public export
data LanguageObject : Language -> Type where
  PromoteObject : LanguageObject Minimal -> LanguageObject HigherOrderInductive
  AtomObject : (l : Language) -> LanguageObject l
  SExpObject : {l : Language} -> LanguageObject l -> LanguageObject l
  SListObject : {l : Language} -> LanguageObject l -> LanguageObject l

public export
Object : Type
Object = DPair Language LanguageObject

public export
gebLanguageObjectToExp : {l : Language} -> LanguageObject l -> GebSExp
gebLanguageObjectToExp {l} (AtomObject l) =
  GAAtom $* [gebLanguageToExp l]
gebLanguageObjectToExp {l} (SExpObject o) =
  GASExp $* [gebLanguageToExp l, gebLanguageObjectToExp o]
gebLanguageObjectToExp {l} (SListObject o) =
  GASList $* [gebLanguageToExp l, gebLanguageObjectToExp o]
gebLanguageObjectToExp {l=Minimal} (PromoteObject o) impossible
gebLanguageObjectToExp {l=HigherOrderInductive} (PromoteObject o) =
  GAPromoteObject $*
    [gebLanguageToExp Minimal, gebLanguageToExp HigherOrderInductive,
     gebLanguageObjectToExp o]

public export
gebObjectToExp : Object -> GebSExp
gebObjectToExp (l ** o) = gebLanguageObjectToExp {l} o

public export
gebExpToObject : GebSExp -> Maybe Object
gebExpToObject (GAPromoteObject $* [oldlx, newlx, ox]) =
  case (gebExpToLanguage oldlx, gebExpToLanguage newlx, gebExpToObject ox) of
    (Just Minimal, Just HigherOrderInductive,
     Just (Minimal ** o)) =>
      Just $ (HigherOrderInductive ** PromoteObject o)
    _ => Nothing
gebExpToObject (GAAtom $* [x]) = case gebExpToLanguage x of
  Just l => Just (l ** AtomObject l)
  _ => Nothing
gebExpToObject (GASExp $* [lx, ox]) =
  case (gebExpToLanguage lx, gebExpToObject ox) of
    (Just l, Just (l' ** o)) => case decEq l l' of
      Yes Refl => Just $ (l ** SExpObject o)
      _ => Nothing
    _ => Nothing
gebExpToObject (GASList $* [lx, ox]) =
  case (gebExpToLanguage lx, gebExpToObject ox) of
    (Just l, Just (l' ** o)) => case decEq l l' of
      Yes Refl => Just $ (l ** SListObject o)
      _ => Nothing
    _ => Nothing
gebExpToObject _ = Nothing

public export
gebLanguageObjectRepresentationComplete : {l : Language} ->
  (o : LanguageObject l) ->
  gebExpToObject (gebLanguageObjectToExp {l} o) = Just (l ** o)
gebLanguageObjectRepresentationComplete
  {l=HigherOrderInductive} (PromoteObject o) =
    rewrite gebLanguageObjectRepresentationComplete o in
    Refl
gebLanguageObjectRepresentationComplete {l} (AtomObject l) =
  rewrite gebLanguageRepresentationComplete l in
  Refl
gebLanguageObjectRepresentationComplete {l} (SExpObject o) =
  rewrite gebLanguageRepresentationComplete l in
  rewrite gebLanguageObjectRepresentationComplete o in
  rewrite decEqRefl decEq l in
  Refl
gebLanguageObjectRepresentationComplete {l} (SListObject o) =
  rewrite gebLanguageRepresentationComplete l in
  rewrite gebLanguageObjectRepresentationComplete o in
  rewrite decEqRefl decEq l in
  Refl

public export
gebObjectRepresentationComplete : (o : Object) ->
  gebExpToObject (gebObjectToExp o) = Just o
gebObjectRepresentationComplete (l ** o) =
  gebLanguageObjectRepresentationComplete {l} o

public export
Show Object where
  show = show . gebObjectToExp

export
objectDecEq : DecEqPred Object
objectDecEq =
  encodingDecEq
    gebObjectToExp
    gebExpToObject
    gebObjectRepresentationComplete
    decEq

public export
DecEq Object where
  decEq = objectDecEq

public export
Eq Object using decEqToEq where
  (==) = (==)

--------------------------------------------------------------------
---- Morphisms of reflective (SExp-based) programming languages ----
--------------------------------------------------------------------

public export
data LanguageMorphism : {l : Language} ->
  (domain, codomain : LanguageObject l) -> Type where
    PromoteMorphism : {domain, codomain : LanguageObject Minimal} ->
      LanguageMorphism {l=Minimal}
        domain codomain ->
      LanguageMorphism {l=HigherOrderInductive}
        (PromoteObject domain) (PromoteObject codomain)
    Identity : {l : Language} -> (o : LanguageObject l) -> LanguageMorphism o o
    Compose : {l : Language} -> (o : LanguageObject l) -> LanguageMorphism o o

public export
Morphism : Type
Morphism = (l : Language **
            domain : LanguageObject l ** codomain : LanguageObject l **
            LanguageMorphism {l} domain codomain)

public export
gebLanguageMorphismToExp :
  {l : Language} -> {domain, codomain : LanguageObject l} ->
  LanguageMorphism domain codomain -> GebSExp
gebLanguageMorphismToExp m = ?gebLanguageMorphismToExp_hole

public export
gebMorphismToExp : Morphism -> GebSExp
gebMorphismToExp (l ** domain ** codomain ** m) =
  gebLanguageMorphismToExp {l} {domain} {codomain} m

public export
gebExpToMorphism : GebSExp -> Maybe Morphism
gebExpToMorphism x = ?gebExpToMorphism_hole

public export
gebLanguageMorphismRepresentationComplete : {l : Language} ->
  {domain, codomain : LanguageObject l} ->
  (m : LanguageMorphism domain codomain) ->
  gebExpToMorphism (gebLanguageMorphismToExp {l} {domain} {codomain} m) =
    Just (l ** domain ** codomain ** m)
gebLanguageMorphismRepresentationComplete {l} {domain} {codomain} m =
  ?gebLanguageMorphismRepresentationComplete_hole

public export
gebMorphismRepresentationComplete : (m : Morphism) ->
  gebExpToMorphism (gebMorphismToExp m) = Just m
gebMorphismRepresentationComplete (l ** domain ** codomain ** m) =
  gebLanguageMorphismRepresentationComplete {l} {domain} {codomain} m

public export
Show Morphism where
  show = show . gebMorphismToExp

export
morphismDecEq : DecEqPred Morphism
morphismDecEq =
  encodingDecEq
    gebMorphismToExp
    gebExpToMorphism
    gebMorphismRepresentationComplete
    decEq

public export
DecEq Morphism where
  decEq = morphismDecEq

public export
Eq Morphism using decEqToEq where
  (==) = (==)

{-
mutual
  public export
  data Morphism : Type where
    Identity : Object -> Morphism
    Compose : (g, f : Morphism) ->
      {auto composable :
        (morphismCodomain f) = (morphismDomain g)} ->
      Morphism
    FromInitial : Object -> Morphism
    ToTerminal : Object -> Morphism
    ProductIntro : (f, g : Morphism) ->
      {auto domainsMatch :
        (morphismDomain f) = (morphismDomain g)} ->
      Morphism
    ProductElimLeft : (a, b : Object) -> Morphism
    ProductElimRight : (a, b : Object) -> Morphism
    CoproductElim : (f, g : Morphism) ->
      {auto codomainsMatch :
        (morphismCodomain f) = (morphismCodomain g)} ->
      Morphism
    CoproductIntroLeft : (a, b : Object) -> Morphism
    CoproductIntroRight : (a, b : Object) -> Morphism
    ExpressionIntro : Object -> Morphism
    ExpressionElim : (exp, exp', eqCase, neqCase : Morphism) ->
      {auto expDomainsMatch :
        (morphismDomain exp) = (morphismDomain exp')} ->
      {auto expCodomainIsExpression :
        (morphismCodomain exp) = ObjectExpression} ->
      {auto expCodomainsMatch :
        (morphismCodomain exp) = (morphismCodomain exp')} ->
      {auto eqDomainMatches :
        (morphismDomain exp) = (morphismDomain eqCase)} ->
      {auto neqDomainMatches :
        (morphismDomain exp) = (morphismDomain neqCase)} ->
      {auto eqCodomainsMatch :
        (morphismCodomain eqCase) = (morphismCodomain neqCase)} ->
      Morphism

  public export
  data MinimalExpression : Type where
    ObjectExp : Object -> MinimalExpression
    MorphismExp : Morphism -> MinimalExpression

  public export
  morphismDomain : Morphism -> Object
  morphismDomain (Identity object) = object
  morphismDomain (Compose g f) = morphismDomain f
  morphismDomain (FromInitial _) = Initial
  morphismDomain (ToTerminal domain) = domain
  morphismDomain (ProductIntro f g) = morphismDomain f
  morphismDomain (ProductElimLeft a b) = Product a b
  morphismDomain (ProductElimRight a b) = Product a b
  morphismDomain (CoproductElim f g) =
    Coproduct (morphismDomain f) (morphismDomain g)
  morphismDomain (CoproductIntroLeft a b) = a
  morphismDomain (CoproductIntroRight a b) = b
  morphismDomain (ExpressionIntro _) = Terminal
  morphismDomain (ExpressionElim exp _ _ _) = morphismDomain exp

  public export
  morphismCodomain : Morphism -> Object
  morphismCodomain (Identity object) = object
  morphismCodomain (Compose g f) = morphismCodomain g
  morphismCodomain (FromInitial codomain) = codomain
  morphismCodomain (ToTerminal _) = Terminal
  morphismCodomain (ProductIntro f g) =
    Product (morphismCodomain f) (morphismCodomain g)
  morphismCodomain (ProductElimLeft a b) = a
  morphismCodomain (ProductElimRight a b) = b
  morphismCodomain (CoproductElim f g) = morphismCodomain f
  morphismCodomain (CoproductIntroLeft a b) = Coproduct a b
  morphismCodomain (CoproductIntroRight a b) = Coproduct a b
  morphismCodomain (ExpressionIntro _) = ObjectExpression
  morphismCodomain (ExpressionElim _ _ eqCase _) =
    morphismCodomain eqCase

mutual
  public export
  gebMinimalExpressionToExp : MinimalExpression -> GebSExp
  gebMinimalExpressionToExp (ObjectExp o) = gebObjectToExp o
  gebMinimalExpressionToExp (MorphismExp m) = gebMorphismToExp m

  public export
  gebMorphismToExp : Morphism -> GebSExp
  gebMorphismToExp (Identity object) =
    GAIdentity $* [gebObjectToExp object]
  gebMorphismToExp (Compose g f) =
    GACompose $* [gebMorphismToExp g, gebMorphismToExp f]
  gebMorphismToExp (FromInitial codomain) =
    GAFromInitial $* [gebObjectToExp codomain]
  gebMorphismToExp (ToTerminal domain) =
    GAToTerminal $* [gebObjectToExp domain]
  gebMorphismToExp (ProductIntro f g) =
    GAProductIntro $* [gebMorphismToExp f, gebMorphismToExp g]
  gebMorphismToExp (ProductElimLeft a b) =
    GAProductElimLeft $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (ProductElimRight a b) =
    GAProductElimRight $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (CoproductElim f g) =
    GACoproductElim $* [gebMorphismToExp f, gebMorphismToExp g]
  gebMorphismToExp (CoproductIntroLeft a b) =
    GACoproductIntroLeft $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (CoproductIntroRight a b) =
    GACoproductIntroRight $* [gebObjectToExp a, gebObjectToExp b]
  gebMorphismToExp (ExpressionIntro x) =
    GAExpressionIntro $* [gebObjectToExp x]
  gebMorphismToExp (ExpressionElim exp exp' eqCase neqCase) =
    GAExpressionElim $*
      [gebMorphismToExp exp,
       gebMorphismToExp exp',
       gebMorphismToExp eqCase,
       gebMorphismToExp neqCase]

public export
gebMorphismExpIsNotObject : (m : Morphism) ->
  gebExpToObject (gebMorphismToExp m) = Nothing
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
  gebExpToMinimalExp x with (gebExpToObject x, gebExpToMorphism x)
    proof p
      gebExpToMinimalExp x | (Just o, Just m) =
        let pfst = PairFstEq p in
        let psnd = PairSndEq p in
        void (gebExpIsNotBothObjectAndMorphism x o m pfst psnd)
      gebExpToMinimalExp x | (Just o, Nothing) = Just $ ObjectExp o
      gebExpToMinimalExp x | (Nothing, Just m) = Just $ MorphismExp m
      gebExpToMinimalExp x | (Nothing, Nothing) = Nothing

  public export
  gebExpToMorphism : GebSExp -> Maybe Morphism
  gebExpToMorphism (GAIdentity $* [objectExp]) =
    case gebExpToObject objectExp of
      Just object => Just $ Identity object
      _ => Nothing
  gebExpToMorphism (GACompose $* [gExp, fExp]) =
    case (gebExpToMorphism gExp, gebExpToMorphism fExp) of
      (Just g, Just f) =>
        case (objectDecEq
          (morphismCodomain f) (morphismDomain g)) of
            Yes composable => Just $ Compose g f {composable}
            No _ => Nothing
      _ => Nothing
  gebExpToMorphism (GAFromInitial $* [codomainExp]) =
    case gebExpToObject codomainExp of
      Just codomain => Just $ FromInitial codomain
      _ => Nothing
  gebExpToMorphism (GAToTerminal $* [domainExp]) =
    case gebExpToObject domainExp of
      Just domain => Just $ ToTerminal domain
      _ => Nothing
  gebExpToMorphism (GAProductIntro $* [fExp, gExp]) =
    case (gebExpToMorphism fExp, gebExpToMorphism gExp) of
      (Just f, Just g) =>
        case (objectDecEq
          (morphismDomain f) (morphismDomain g)) of
            Yes domainsMatch => Just $ ProductIntro f g {domainsMatch}
            No _ => Nothing
      _ => Nothing
  gebExpToMorphism (GAProductElimLeft $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ ProductElimLeft a b
      _ => Nothing
  gebExpToMorphism (GAProductElimRight $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ ProductElimRight a b
      _ => Nothing
  gebExpToMorphism (GACoproductElim $* [fExp, gExp]) =
    case (gebExpToMorphism fExp, gebExpToMorphism gExp) of
      (Just f, Just g) =>
        case (objectDecEq
          (morphismCodomain f) (morphismCodomain g)) of
            Yes codomainsMatch => Just $ CoproductElim f g {codomainsMatch}
            No _ => Nothing
      _ => Nothing
  gebExpToMorphism (GACoproductIntroLeft $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ CoproductIntroLeft a b
      _ => Nothing
  gebExpToMorphism (GACoproductIntroRight $* [aExp, bExp]) =
    case (gebExpToObject aExp, gebExpToObject bExp) of
      (Just a, Just b) => Just $ CoproductIntroRight a b
      _ => Nothing
  gebExpToMorphism (GAExpressionIntro $* [x]) =
    case gebExpToObject x of
      Just minimalObj => Just $ ExpressionIntro minimalObj
      _ => Nothing
  gebExpToMorphism (GAExpressionElim $* [exp, exp', eqExp, neqExp]) =
    case (gebExpToMorphism exp, gebExpToMorphism exp',
          gebExpToMorphism eqExp, gebExpToMorphism neqExp) of
      (Just exp, Just exp', Just eqCase, Just neqCase) =>
        case
          (objectDecEq
            (morphismDomain exp) (morphismDomain exp'),
           objectDecEq (morphismCodomain exp) ObjectExpression,
           objectDecEq
            (morphismCodomain exp) (morphismCodomain exp')) of
              (Yes domainsMatch, Yes expCodomainIsExpression,
              Yes expCodomainsMatch) =>
                case
                  (objectDecEq
                    (morphismDomain exp)
                    (morphismDomain eqCase),
                  objectDecEq
                    (morphismDomain exp)
                    (morphismDomain neqCase),
                  objectDecEq
                    (morphismCodomain eqCase)
                    (morphismCodomain neqCase)) of
                (Yes eqDomainsMatch, Yes neqDomainsMatch, Yes codomainsMatch) =>
                  Just $ ExpressionElim exp exp' eqCase neqCase
                _ => Nothing
              _ => Nothing
      _ => Nothing
  gebExpToMorphism _ = Nothing

  public export
  gebExpIsNotBothObjectAndMorphism : (x : GebSExp) ->
    (o : Object) -> (m : Morphism) ->
    gebExpToObject x = Just o -> gebExpToMorphism x = Just m ->
    Void
  gebExpIsNotBothObjectAndMorphism (GALanguage $* _) _ _ eqo eqm =
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
gebObjectExpIsNotMorphism : (o : Object) ->
  gebExpToMorphism (gebObjectToExp o) = Nothing
gebObjectExpIsNotMorphism Initial = Refl
gebObjectExpIsNotMorphism Terminal = Refl
gebObjectExpIsNotMorphism (Product _ _) = Refl
gebObjectExpIsNotMorphism (Coproduct _ _) = Refl
gebObjectExpIsNotMorphism ObjectExpression = Refl
gebObjectExpIsNotMorphism (MorphismExpression _ _) = Refl

public export
gebMorphismRepresentationComplete : (r : Morphism) ->
  gebExpToMorphism (gebMorphismToExp r) = Just r
gebMorphismRepresentationComplete (Identity object) =
  rewrite gebObjectRepresentationComplete object in
  Refl
gebMorphismRepresentationComplete (Compose g f {composable}) =
  rewrite gebMorphismRepresentationComplete g in
  rewrite gebMorphismRepresentationComplete f in
  rewrite composable in
  rewrite decEqRefl objectDecEq (morphismDomain g) in
  rewrite uip composable _ in
  Refl
gebMorphismRepresentationComplete (FromInitial codomain) =
  rewrite gebObjectRepresentationComplete codomain in
  Refl
gebMorphismRepresentationComplete (ToTerminal domain) =
  rewrite gebObjectRepresentationComplete domain in
  Refl
gebMorphismRepresentationComplete (ProductIntro f g {domainsMatch}) =
  rewrite gebMorphismRepresentationComplete f in
  rewrite gebMorphismRepresentationComplete g in
  rewrite domainsMatch in
  rewrite decEqRefl objectDecEq (morphismDomain g) in
  rewrite uip domainsMatch _ in
  Refl
gebMorphismRepresentationComplete (ProductElimLeft a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (ProductElimRight a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (CoproductElim f g {codomainsMatch}) =
  rewrite gebMorphismRepresentationComplete f in
  rewrite gebMorphismRepresentationComplete g in
  rewrite codomainsMatch in
  rewrite decEqRefl objectDecEq (morphismCodomain g) in
  rewrite uip codomainsMatch _ in
  Refl
gebMorphismRepresentationComplete (CoproductIntroLeft a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (CoproductIntroRight a b) =
  rewrite gebObjectRepresentationComplete a in
  rewrite gebObjectRepresentationComplete b in
  Refl
gebMorphismRepresentationComplete (ExpressionIntro o) =
  rewrite gebObjectRepresentationComplete o in
  Refl
gebMorphismRepresentationComplete
  (ExpressionElim exp exp' eqCase neqCase
    {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
    {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) =
      rewrite gebMorphismRepresentationComplete exp in
      rewrite gebMorphismRepresentationComplete exp' in
      rewrite gebMorphismRepresentationComplete eqCase in
      rewrite gebMorphismRepresentationComplete neqCase in
      rewrite sym expDomainsMatch in
      rewrite sym expCodomainIsExpression in
      rewrite expCodomainsMatch in
      rewrite decEqRefl objectDecEq (morphismDomain exp) in
      rewrite decEqRefl objectDecEq (morphismCodomain exp') in
      rewrite sym eqDomainMatches in
      rewrite decEqRefl objectDecEq (morphismDomain exp) in
      rewrite sym neqDomainMatches in
      rewrite decEqRefl objectDecEq (morphismDomain exp) in
      rewrite sym eqCodomainsMatch in
      rewrite decEqRefl objectDecEq (morphismCodomain eqCase) in
      rewrite uip eqCodomainsMatch _ in
      rewrite uip neqDomainMatches _ in
      rewrite uip eqDomainMatches _ in
      rewrite uip expCodomainsMatch _ in
      rewrite uip expCodomainIsExpression _ in
      rewrite uip expDomainsMatch _ in
      Refl

export
morphismDecEq : DecEqPred Morphism
morphismDecEq =
  encodingDecEq
    gebMorphismToExp
    gebExpToMorphism
    gebMorphismRepresentationComplete
    decEq

public export
gebMinimalExpRepresentationComplete : (r : MinimalExpression) ->
  gebExpToMinimalExp (gebMinimalExpressionToExp r) = Just r
gebMinimalExpRepresentationComplete (ObjectExp o) =
  rewrite gebObjectExpIsNotMorphism o in
  rewrite gebObjectRepresentationComplete o in
  Refl
gebMinimalExpRepresentationComplete (MorphismExp m) =
  rewrite gebMorphismExpIsNotObject m in
  rewrite gebMorphismRepresentationComplete m in
  Refl

public export
DecEq Morphism where
  decEq = morphismDecEq

public export
Eq Morphism using decEqToEq where
  (==) = (==)

public export
Show Morphism where
  show m = show (gebMorphismToExp m)

public export
minimalExpressionDecEq : DecEqPred MinimalExpression
minimalExpressionDecEq (ObjectExp x) (ObjectExp x') =
  case decEq x x' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
minimalExpressionDecEq (ObjectExp x) (MorphismExp x') =
  No $ \eq => case eq of Refl impossible
minimalExpressionDecEq (MorphismExp x) (ObjectExp x') =
  No $ \eq => case eq of Refl impossible
minimalExpressionDecEq (MorphismExp x) (MorphismExp x') =
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
interpretObject : Object -> Type
interpretObject Initial = Void
interpretObject Terminal = ()
interpretObject (Product r r') =
  (interpretObject r, interpretObject r')
interpretObject (Coproduct r r') =
  Either (interpretObject r) (interpretObject r')
interpretObject ObjectExpression = Object
interpretObject (MorphismExpression domain codomain) =
  (m : Morphism **
   (morphismDomain m = domain, morphismCodomain m = codomain))

public export
interpretMorphismDomain : Morphism -> Type
interpretMorphismDomain r =
  interpretObject (morphismDomain r)

public export
interpretMorphismCodomain : Morphism -> Type
interpretMorphismCodomain r =
  interpretObject (morphismCodomain r)

public export
interpretMorphismType : Morphism -> Type
interpretMorphismType r =
  interpretMorphismDomain r -> interpretMorphismCodomain r

public export
interpretMorphism : (r : Morphism) ->
  interpretMorphismType r
interpretMorphism (Identity o) x = x
interpretMorphism (Compose g f {composable}) x =
  interpretMorphism g $
    replace {p=interpretObject} composable $
      interpretMorphism f x
interpretMorphism (FromInitial _) x = void x
interpretMorphism (ToTerminal _) _ = ()
interpretMorphism (ProductIntro f g {domainsMatch}) x =
  (interpretMorphism f x,
   interpretMorphism g (rewrite sym domainsMatch in x))
interpretMorphism (ProductElimLeft a b) x = fst x
interpretMorphism (ProductElimRight a b) x = snd x
interpretMorphism (CoproductElim f g {codomainsMatch}) x =
  case x of
    Left x' => interpretMorphism f x'
    Right x' => rewrite codomainsMatch in interpretMorphism g x'
interpretMorphism (CoproductIntroLeft a b) x = Left x
interpretMorphism (CoproductIntroRight a b) x = Right x
interpretMorphism (ExpressionIntro exp) () = exp
interpretMorphism (ExpressionElim exp exp' eqCase neqCase
  {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
  {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) x =
    let
      y = interpretMorphism exp x
      y' = replace {p=interpretObject} expCodomainIsExpression y
      z = interpretMorphism exp' (rewrite sym expDomainsMatch in x)
      z' = replace {p=interpretObject} (sym expCodomainsMatch) z
      z'' = replace {p=interpretObject} expCodomainIsExpression z'
    in
    if y' == z'' then
      interpretMorphism eqCase (rewrite sym eqDomainMatches in x)
    else
      rewrite eqCodomainsMatch in
      interpretMorphism neqCase (rewrite sym neqDomainMatches in x)

-----------------------------------
---- Correctness of reflection ----
-----------------------------------

public export
objectQuote : Object -> interpretObject ObjectExpression
objectQuote = Prelude.id

public export
objectUnquote : interpretObject ObjectExpression -> Object
objectUnquote = Prelude.id

export
objectUnquoteQuoteCorrect : (r : Object) ->
  objectUnquote (objectQuote r) = r
objectUnquoteQuoteCorrect r = Refl

------------------------------------------------------
---- Morphism transformations ("compiler passes") ----
------------------------------------------------------

public export
MorphismTransform : Type
MorphismTransform = Morphism -> Morphism

-- | A correct morphism transformation preserves the morphism's domain.
public export
MorphismTransformDomainCorrect : MorphismTransform -> Type
MorphismTransformDomainCorrect transform = (m : Morphism) ->
  interpretMorphismDomain (transform m) =
    interpretMorphismDomain m

-- | A correct morphism transformation preserves the morphism's codomain.
public export
MorphismTransformCodomainCorrect : MorphismTransform -> Type
MorphismTransformCodomainCorrect transform = (m : Morphism) ->
  interpretMorphismCodomain (transform m) =
    interpretMorphismCodomain m

-- | A correct morphism transformation preserves extensional equality.
public export
MorphismTransformCorrect : (transform : MorphismTransform) ->
  (domainTransformCorrect :
    MorphismTransformDomainCorrect transform) ->
  (codomainTransformCorrect :
    MorphismTransformCodomainCorrect transform) ->
  Type
MorphismTransformCorrect
  transform domainTransformCorrect codomainTransformCorrect =
    (m : Morphism) ->
    (x : interpretMorphismDomain m) ->
      (rewrite sym (codomainTransformCorrect m) in
       interpretMorphism (transform m)
         (rewrite domainTransformCorrect m in x)) =
       interpretMorphism m x

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
  MinimalTypeTerm : (type : Object) -> MinimalTermType
  MorphismTerm : (domain, codomain : Object) -> MinimalTermType

public export
data MinimalTerm : (numApplications : Nat) -> MinimalTermType -> Type where
  UnappliedMorphismTerm : (morphism : Morphism) ->
    MinimalTerm 0 $
      MorphismTerm
        (morphismDomain morphism)
        (morphismCodomain morphism)
  Application : {morphismApplications, termApplications : Nat} ->
    {domain, codomain : Object} ->
    MinimalTerm morphismApplications (MorphismTerm domain codomain) ->
    MinimalTerm termApplications (MinimalTypeTerm domain) ->
    MinimalTerm
      (S $ morphismApplications + termApplications) (MinimalTypeTerm codomain)
  ExFalsoTerm : {numApplications : Nat} -> {type : Object} ->
    MinimalTerm numApplications (MinimalTypeTerm Initial) ->
    MinimalTerm numApplications $ MinimalTypeTerm type
  UnitTerm : MinimalTerm 0 $ MinimalTypeTerm Terminal
  PairTerm : {leftApplications, rightApplications : Nat} ->
    {left, right : Object} ->
    MinimalTerm leftApplications (MinimalTypeTerm left) ->
    MinimalTerm rightApplications (MinimalTypeTerm right) ->
    MinimalTerm (leftApplications + rightApplications) $
      MinimalTypeTerm $ Product left right
  MinimalLeft :
    {leftApplications : Nat} -> {left : Object} ->
    MinimalTerm leftApplications (MinimalTypeTerm left) ->
    (right : Object) ->
    MinimalTerm leftApplications $ MinimalTypeTerm $ Coproduct left right
  MinimalRight :
    (left : Object) ->
    {rightApplications : Nat} -> {right : Object} ->
    MinimalTerm rightApplications (MinimalTypeTerm right) ->
    MinimalTerm rightApplications $ MinimalTypeTerm $ Coproduct left right
  ExpressionTerm : Object ->
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
  GAMorphismTerm $* [gebMorphismToExp morphism]
gebMinimalTermToExp {type=(MinimalTypeTerm type)} (ExFalsoTerm ti) =
  GAExFalsoTerm $* [gebMinimalTermToExp ti, gebObjectToExp type]
gebMinimalTermToExp UnitTerm = $^ GAUnitTerm
gebMinimalTermToExp
  (PairTerm {leftApplications} {rightApplications} {left} {right}
   leftTerm rightTerm) =
    GAPairTerm $* [gebMinimalTermToExp leftTerm, gebMinimalTermToExp rightTerm]
gebMinimalTermToExp {numApplications} (MinimalLeft left right) =
  GALeftTerm $* [gebMinimalTermToExp left, gebObjectToExp right]
gebMinimalTermToExp {numApplications} (MinimalRight left right) =
  GARightTerm $* [gebObjectToExp left, gebMinimalTermToExp right]
gebMinimalTermToExp (ExpressionTerm x) =
  GAExpressionTerm $* [gebObjectToExp x]

public export
gebExpToMinimalTerm :
  GebSExp -> Maybe (type : MinimalTermType ** n : Nat ** MinimalTerm n type)
gebExpToMinimalTerm (GAMorphismTerm $* [x]) =
  case gebExpToMorphism x of
    Just morphism => Just
      (MorphismTerm
        (morphismDomain morphism)
        (morphismCodomain morphism) **
       0 **
       (UnappliedMorphismTerm morphism))
    Nothing => Nothing
gebExpToMinimalTerm (GAExFalsoTerm $* [ti, ty]) =
  case (gebExpToMinimalTerm ti, gebExpToObject ty) of
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
        MorphismTerm domain codomain =>
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
  case (gebExpToMinimalTerm leftExp, gebExpToObject rightExp) of
    (Just (MinimalTypeTerm leftObject ** nLeft ** leftTerm),
     Just rightObject) =>
      Just
        (MinimalTypeTerm (Coproduct leftObject rightObject) **
         nLeft **
         MinimalLeft leftTerm rightObject)
    _ => Nothing
gebExpToMinimalTerm (GARightTerm $* [leftExp, rightExp]) =
  case (gebExpToObject leftExp, gebExpToMinimalTerm rightExp) of
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
  rewrite decEqRefl objectDecEq domain in
  Refl
gebMinimalTermRepresentationComplete
  (UnappliedMorphismTerm morphism) =
    rewrite gebMorphismRepresentationComplete morphism in
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
interpretMinimalTermType (MinimalTypeTerm type) = interpretObject type
interpretMinimalTermType (MorphismTerm domain codomain) =
  interpretObject domain -> interpretObject codomain

public export
interpretMinimalTerm : {type : MinimalTermType} -> {numApplications : Nat} ->
  (term : MinimalTerm numApplications type) -> interpretMinimalTermType type
interpretMinimalTerm (Application f x) =
  interpretMinimalTerm f $ interpretMinimalTerm x
interpretMinimalTerm (UnappliedMorphismTerm morphism) =
  interpretMorphism morphism
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
correctMorphismTransformPreservesTermInterpretation :
  (transform : MorphismTransform) ->
  {domainTransformCorrect :
    MorphismTransformDomainCorrect transform} ->
  {codomainTransformCorrect :
    MorphismTransformCodomainCorrect transform} ->
  MorphismTransformCorrect
    transform domainTransformCorrect codomainTransformCorrect ->
  (m : Morphism) ->
  {numApplications : Nat} ->
  (term :
    MinimalTerm numApplications
      (MinimalTypeTerm (morphismDomain m))) ->
  (term' :
    MinimalTerm numApplications
      (MinimalTypeTerm (morphismDomain (transform m)))) ->
  interpretMinimalTerm term =
    (rewrite sym (domainTransformCorrect m) in (interpretMinimalTerm term')) ->
  interpretMinimalTerm
    (Application (UnappliedMorphismTerm m) term) =
  (rewrite sym (codomainTransformCorrect m) in (interpretMinimalTerm
    (Application (UnappliedMorphismTerm (transform m)) term')))
correctMorphismTransformPreservesTermInterpretation
  transform transformCorrect m {numApplications} term term' termEq =
    ?correctMorphismTransformPreservesTermInterpretation_hole

public export
bigStepMorphismReduction :
  (m : Morphism) ->
  MinimalFullyAppliedTerm (MinimalTypeTerm (morphismDomain m)) ->
  MinimalFullyAppliedTerm (MinimalTypeTerm (morphismCodomain m))
bigStepMorphismReduction (Identity _) x = x
bigStepMorphismReduction (Compose g f {composable}) x =
  bigStepMorphismReduction g $
    rewrite sym composable in (bigStepMorphismReduction f x)
bigStepMorphismReduction (FromInitial _) x = ExFalsoTerm x
bigStepMorphismReduction (ToTerminal y) x = UnitTerm
bigStepMorphismReduction (ProductIntro f g {domainsMatch}) x =
  PairTerm
    (bigStepMorphismReduction f x)
    (bigStepMorphismReduction g $ rewrite sym domainsMatch in x)
bigStepMorphismReduction (ProductElimLeft a b) x = case x of
  PairTerm {leftApplications=0} {rightApplications=0} left right => left
  ExFalsoTerm ti => ExFalsoTerm ti
bigStepMorphismReduction (ProductElimRight a b) x = case x of
  PairTerm {leftApplications=0} {rightApplications=0} left right => right
  ExFalsoTerm ti => ExFalsoTerm ti
bigStepMorphismReduction (CoproductElim f g {codomainsMatch}) x =
  case x of
    MinimalLeft left _ =>
      bigStepMorphismReduction f left
    MinimalRight _ right =>
      rewrite codomainsMatch in bigStepMorphismReduction g right
    ExFalsoTerm ti => ExFalsoTerm ti
bigStepMorphismReduction (CoproductIntroLeft left right) x =
  MinimalLeft x right
bigStepMorphismReduction (CoproductIntroRight left right) x =
  MinimalRight left x
bigStepMorphismReduction (ExpressionIntro exp) _ = ExpressionTerm exp
bigStepMorphismReduction (ExpressionElim exp exp' eqCase neqCase
  {expDomainsMatch} {expCodomainIsExpression} {expCodomainsMatch}
  {eqDomainMatches} {neqDomainMatches} {eqCodomainsMatch}) x =
    let
      xReduced = bigStepMorphismReduction exp x
      xReduced' = bigStepMorphismReduction exp'
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
        bigStepMorphismReduction
          eqCase (rewrite sym eqDomainMatches in x)
      eqCaseReduced' =
        bigStepMorphismReduction
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
        bigStepMorphismReduction m xReduced
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
  bigStepMorphismReductionCorrect :
    (m : Morphism) ->
    (x : MinimalFullyAppliedTerm (MinimalTypeTerm (morphismDomain m))) ->
    interpretMinimalTerm (bigStepMorphismReduction m x) =
      interpretMinimalTerm (UnappliedMorphismTerm m) (interpretMinimalTerm x)
  bigStepMorphismReductionCorrect m x =
    ?bigStepMorphismReductionCorrect_hole

  public export
  bigStepMinimalTermReductionCorrect :
    {type : MinimalTermType} -> {numApplications : Nat} ->
    (term : MinimalTerm numApplications type) ->
    interpretMinimalTerm (bigStepMinimalTermReduction term) =
      interpretMinimalTerm term
  bigStepMinimalTermReductionCorrect {type} term =
    ?bigStepMinimalTermReductionCorrect_hole

public export
smallStepMorphismReduction :
  (m : Morphism) ->
  {numApplications : Nat} ->
  MinimalTerm numApplications (MinimalTypeTerm (morphismDomain m)) ->
  (remainingApplications : Nat **
   MinimalTerm
    remainingApplications (MinimalTypeTerm (morphismCodomain m)))
smallStepMorphismReduction (Identity x) term =
  ?smallStepMorphismReduction_hole_ident
smallStepMorphismReduction (Compose g f) term =
  ?smallStepMorphismReduction_hole_compose
smallStepMorphismReduction (FromInitial x) term =
  ?smallStepMorphismReduction_hole_frominit
smallStepMorphismReduction (ToTerminal x) term =
  ?smallStepMorphismReduction_hole_toterm
smallStepMorphismReduction (ProductIntro f g) term =
  ?smallStepMorphismReduction_hole_prodintro
smallStepMorphismReduction (ProductElimLeft a b) term =
  ?smallStepMorphismReduction_hole_prodleft
smallStepMorphismReduction (ProductElimRight a b) term =
  ?smallStepMorphismReduction_hole_prodright
smallStepMorphismReduction (CoproductElim f g) term =
  ?smallStepMorphismReduction_hole_coelim
smallStepMorphismReduction (CoproductIntroLeft a b) term =
  ?smallStepMorphismReduction_hole_cointroleft
smallStepMorphismReduction (CoproductIntroRight a b) term =
  ?smallStepMorphismReduction_hole_cointroright
smallStepMorphismReduction (ExpressionIntro x) term =
  ?smallStepMorphismReduction_hole_expIntro
smallStepMorphismReduction
  (ExpressionElim exp exp' eqCase neqCase) term =
    ?smallStepMorphismReduction_hole_expElim

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

---------------------------------------------------------------------------
---- Work for after self-hosting: parameterized user-defined languages ----
---------------------------------------------------------------------------

public export
data LanguageSort : Type where
  LogicSort : LanguageSort
  MachineSort : LanguageSort
  GeneralSort : LanguageSort

public export
data Kind : Type where
  KStar : LanguageSort -> Kind
  KArrow : Kind -> Kind -> Kind

public export
data ParameterizedLanguage : Kind -> Type where
  ParameterizedMinimal : ParameterizedLanguage (KStar LogicSort)
  ParameterizedHigherOrderInductive : ParameterizedLanguage (KStar LogicSort)
