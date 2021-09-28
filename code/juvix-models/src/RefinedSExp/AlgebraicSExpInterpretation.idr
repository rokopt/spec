module RefinedSExp.AlgebraicSExpInterpretation

import public RefinedSExp.AlgebraicSExp
import Data.Maybe
import Library.List

{-
 - XXX Make total either by interpreting to signatures, or making
 - S-expressions the only possible target of a refined "maybe" (and
 - using that in concert with reflection), or by finding a way to show
 - Idris that the representation argument always decreases.
 -}
%default partial

mutual
  public export total
  interpretRefinement : (representation : RefinedSExp) ->
    {auto checked : CheckedRefinement representation} -> Type
  interpretRefinement (RAVoid $* []) = Void
  interpretRefinement (RAUnit $* []) = Unit

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
    (RefinedExponential domainRep codomainRep {domainValid} {codomainValid}) =
      interpretRefinedObject {representation=domainRep}
        (sexpRepresentedObject domainValid) ->
      interpretRefinedObject {representation=codomainRep}
        (sexpRepresentedObject codomainValid)
  interpretRefinedObject RefinedNat = Nat
  interpretRefinedObject ReflectedAtom = RefinedAtom
  interpretRefinedObject ReflectedExp = RefinedSExp
  interpretRefinedObject ReflectedList = RefinedSList
  interpretRefinedObject (RefinedMaybe objectRep {objectValid}) =
    Maybe
      (interpretRefinedObject {representation=objectRep}
        (sexpRepresentedObject objectValid))
  interpretRefinedObject
    {representation=(RSMaybeRefinement objectRep testCodomainRep testRep)}
    (MaybeRefinement {objectRep} {testCodomainRep} object testCodomain test) =
      (x : interpretRefinedObject object **
       let
        m =
          interpretRefinedMorphism
            {representation=testRep}
            {codomainRep=(RAMaybe $*** testCodomainRep)}
            {domain=object}
            {codomain=
              (RefinedMaybe testCodomainRep
                {objectValid=(objectEnsuresRepresentation testCodomain)})}
            test
            x
       in
       ?interpretRefinedObject_mayberefinement_hole)

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
    interpretRefinedObject {representation=domainRep} domain ->
    interpretRefinedObject {representation=codomainRep} codomain
  interpretRefinedMorphism {domain} (RefinedFromVoid _) =
    case domain of
      RefinedVoid => \v : Void => void v
  interpretRefinedMorphism {codomain} (RefinedToUnit _) =
    case codomain of
      RefinedUnit => \v => ()
  interpretRefinedMorphism {domain} {codomain} (RefinedIdentity object) =
    rewrite (objectRepresentationUnique domain codomain) in id
  interpretRefinedMorphism
    -- {representation=(RACompose $* [leftRep, rightRep])}
    {domain} {codomain}
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
    {domain} {codomain=(RefinedMaybe domainRep {objectValid})} (RefinedJust _) =
      rewrite objectRepresentationUnique (IsJustElim objectValid) domain in
      Just
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
