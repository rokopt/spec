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

  public export
  interpretRefinedProduct : {representations : RefinedSList} ->
    ListForAll RefinedObject representation -> Type
  interpretRefinedProduct ListForAllEmpty = ()
  interpretRefinedProduct
    (ListForAllCons {l} head tail) =
      (interpretRefinedObject head,
       interpretRefinedProduct {representations=l} tail)

  public export
  interpretRefinedCoproduct : {representations : RefinedSList} ->
    ListForAll RefinedObject representation -> Type
  interpretRefinedCoproduct ListForAllEmpty = Void
  interpretRefinedCoproduct
    (ListForAllCons {l} head tail) =
      Either
        (interpretRefinedObject head)
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
      RefinedUnit impossible
  interpretRefinedMorphism {codomain} (RefinedToUnit _) =
    case codomain of
      RefinedVoid impossible
      RefinedUnit => \v => ()
  interpretRefinedMorphism {domain} {codomain} (RefinedIdentity object) =
    rewrite (objectRepresentationUnique domain codomain) in id
  interpretRefinedMorphism {domain} {codomain} (RefinedCompose {a} {b} {c} left right) =
    let
      domLeftCorrect = refinedMorphismDomainCorrect left
      codRightCorrect = refinedMorphismCodomainCorrect right
      domLeftEqualsCodRight =
        justInjective $ trans (sym domLeftCorrect) codRightCorrect
      lm =
        interpretRefinedMorphism
          {domain=(refinedMorphismDomain left)} {codomain} left
      rm =
        interpretRefinedMorphism
          {domain} {codomain=(refinedMorphismCodomain right)} right
      lm' =
        replace
          {p=
            (\m => interpretRefinedObject m -> interpretRefinedObject codomain)}
          domLeftEqualsCodRight
          lm
    in
    lm' . rm

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
