module RefinedSExp.AlgebraicSExpInterpretation

import public RefinedSExp.AlgebraicSExp
import Data.Maybe
import Library.List

%default total

public export
Contract : {domain, codomain : Type} -> (f : domain -> codomain) -> Type
Contract {domain} {codomain} f =
  (P : domain -> Type ** Q : codomain -> Type ** (x : domain) -> P x -> Q (f x))

mutual
  public export
  interpretRefinedObject :
    {representation : RefinedSExp} -> RefinedObject representation -> Type
  interpretRefinedObject RefinedVoid = Void
  interpretRefinedObject RefinedUnit = ()
  interpretRefinedObject (RefinedProduct {representations} objects) =
    interpretRefinedProduct {representations} objects
  interpretRefinedObject (RefinedCoproduct {representations} objects) =
    interpretRefinedCoproduct {representations} objects
  interpretRefinedObject
    (RefinedExponential {domainRep} {codomainRep} domain codomain) =
      interpretRefinedObject {representation=domainRep} domain ->
      interpretRefinedObject {representation=codomainRep} codomain
  interpretRefinedObject RefinedNat = Nat
  interpretRefinedObject ReflectedAtom = RefinedAtom
  interpretRefinedObject ReflectedExp = RefinedSExp
  interpretRefinedObject ReflectedList = RefinedSList
  interpretRefinedObject {representation=(RSMaybe objectRep)}
    (RefinedMaybe object) =
      Maybe (interpretRefinedObject {representation=objectRep} object)
  interpretRefinedObject
    {representation=(RSMaybeRefinement objectRep testCodomainRep testRep)}
    (MaybeRefinement {objectRep} {testCodomainRep} object testCodomain test) =
      let
        m =
          interpretRefinedMorphism
            {representation=testRep}
            {codomainRep=(RAMaybe $*** testCodomainRep)}
            {domain=object}
            {codomain=(RefinedMaybe testCodomain)}
            test
      in
      (x : interpretRefinedObject object **
       IsJust
        {a=(interpretRefinedObject
          {representation=testCodomainRep} testCodomain)} $
            ?interpretRefinedObject_maybe_refinement_hole {- XXX (m x) -} )

  public export
  interpretRefinedProduct : {representations : RefinedSList} ->
    ListForAll RefinedObject representations -> Type
  interpretRefinedProduct {representations=[]} ListForAllEmpty = ()
  interpretRefinedProduct
    {representations=(x :: l)}
    (ListForAllCons head tail) =
      (interpretRefinedObject {representation=x} head,
       interpretRefinedProduct {representations=l} tail)

  public export
  interpretRefinedCoproduct : {representations : RefinedSList} ->
    ListForAll RefinedObject representations -> Type
  interpretRefinedCoproduct ListForAllEmpty = Void
  interpretRefinedCoproduct
    {representations=(x :: l)}
    (ListForAllCons head tail) =
      Either
        (interpretRefinedObject {representation=x} head)
        (interpretRefinedCoproduct {representations=l} tail)

  public export
  interpretRefinedMorphism :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    {domain : RefinedObject domainRep} ->
    {codomain : RefinedObject codomainRep} ->
    RefinedMorphism representation domainRep codomainRep ->
    (interpretRefinedObject domain -> interpretRefinedObject codomain)
  interpretRefinedMorphism {domain} (RefinedFromVoid _) =
    case domain of
      RefinedVoid => \v : Void => void v
  interpretRefinedMorphism {codomain} (RefinedToUnit _) =
    case codomain of
      RefinedUnit => \v => ()
  interpretRefinedMorphism {domain} {codomain} (RefinedIdentity object) =
    rewrite (objectRepresentationUnique domain codomain) in id
  interpretRefinedMorphism {domain} {codomain}
    (RefinedCompose {a} {b} {c} {leftRep} {rightRep} left right) =
      let
        domLeftCorrect = refinedMorphismDomainCorrect left
        codRightCorrect = refinedMorphismCodomainCorrect right
        domLeftEqualsCodRight =
          justInjective $ trans (sym domLeftCorrect) codRightCorrect
        lm =
          interpretRefinedMorphism {representation=leftRep}
            {domain=(refinedMorphismDomain left)} {codomain} left
        rm =
          interpretRefinedMorphism {representation=rightRep}
            {domain} {codomain=(refinedMorphismCodomain right)} right
        lm' =
          replace
            {p=
              (\d =>
                interpretRefinedObject {representation=b} d ->
                interpretRefinedObject {representation=c} codomain)}
            domLeftEqualsCodRight
            lm
      in
      lm' . rm
  interpretRefinedMorphism {codomain} (RefinedZero _) =
    case codomain of
      RefinedNat => \_ => Z
  interpretRefinedMorphism
    {domain=RefinedNat} {codomain=RefinedNat} RefinedSuccessor =
      S
  interpretRefinedMorphism {codomain} (RefinedNil _) =
    case codomain of
      ReflectedList => \_ => []
  interpretRefinedMorphism {domainRep} {codomainRep=(RSMaybe domainRep)}
    {domain} {codomain=(RefinedMaybe domain')} (RefinedJust _) =
      rewrite objectRepresentationUnique domain domain' in Just
  interpretRefinedMorphism {codomain=(RefinedMaybe codomain')}
    (RefinedNothing _ _) =
      \_ => Nothing

  public export
  interpretRefinedContract :
    {representation, domainRep, codomainRep, subjectMorphismRep :
      RefinedSExp} ->
    {domain : RefinedObject domainRep} ->
    {codomain : RefinedObject codomainRep} ->
    {subjectMorphism :
      RefinedMorphism subjectMorphismRep domainRep codomainRep} ->
    RefinedContract representation domainRep codomainRep subjectMorphismRep ->
    Contract (interpretRefinedMorphism {domain} {codomain} subjectMorphism)
  interpretRefinedContract _ impossible
