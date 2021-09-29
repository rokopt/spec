module RefinedSExp.AlgebraicSExpInterpretation

import public RefinedSExp.AlgebraicSExp
import Data.Maybe
import Library.List

%default total

public export
ComputableFunction : Type
ComputableFunction = RefinedSExp -> Maybe RefinedSExp

infixl 1 #.
public export
(#.) : ComputableFunction -> ComputableFunction -> ComputableFunction
g #. f = f >=> g

mutual
  public export
  interpretFunction : (representation : RefinedSExp) ->
    {auto checked : CheckedFunction representation} ->
    ComputableFunction
  interpretFunction (RACompose $* [g, f]) {checked} =
    interpretFunction g {checked=(andLeft checked)} #.
      interpretFunction f {checked=(andRight checked)}

  public export
  interpretFunctionList : (representation : RefinedSList) ->
    {auto checked : CheckedFunctionList representation} ->
    List ComputableFunction
  interpretFunctionList [] = []
  interpretFunctionList (x :: l) {checked} =
    interpretFunction x {checked=(andLeft checked)} ::
    interpretFunctionList l {checked=(andRight checked)}

  public export
  interpretRefinement : (representation : RefinedSExp) ->
    {auto checked : CheckedRefinement representation} -> Type
  interpretRefinement (RAVoid $* []) = Void
  interpretRefinement (RAUnit $* []) = Unit

  public export
  interpretRefinementList : (representation : RefinedSList) ->
    {auto checked : CheckedRefinementList representation} -> List Type
  interpretRefinementList [] = []
  interpretRefinementList (x :: l) {checked} =
    interpretRefinement x {checked=(andLeft checked)} ::
    interpretRefinementList l {checked=(andRight checked)}

  public export
  InterpretedMorphismType :
    (representation, domainRep, codomainRep : RefinedSExp) ->
    {auto domainChecked : CheckedRefinement domainRep} ->
    {auto codomainChecked : CheckedRefinement codomainRep} ->
    {auto checked : CheckedMorphism representation domainRep codomainRep} ->
    Type
  InterpretedMorphismType representation domainRep codomainRep {checked} =
    interpretRefinement domainRep -> interpretRefinement codomainRep

  public export
  interpretMorphism : (representation, domainRep, codomainRep : RefinedSExp) ->
    {auto domainChecked : CheckedRefinement domainRep} ->
    {auto codomainChecked : CheckedRefinement codomainRep} ->
    {auto checked : CheckedMorphism representation domainRep codomainRep} ->
    InterpretedMorphismType representation domainRep codomainRep {checked}
  interpretMorphism (RAFromVoid $* [domain]) (RAVoid $* []) domain' {checked} =
    \x => void x
  interpretMorphism (RAToUnit $* [codomain]) codomain' (RAUnit $* []) =
    \_ => ()

  public export
  data InterpretedMorphismList :
    (representation, domains, codomains : RefinedSList) ->
    {auto domainsChecked : CheckedRefinementList domains} ->
    {auto codomainsChecked : CheckedRefinementList codomains} ->
    {auto checked : CheckedMorphismList representation domains codomains} ->
    Type where
      EmptyInterpretedMorphismList : InterpretedMorphismList [] [] []
      InterpretedMorphismListCons :
        {headRep, headDom, headCodom : RefinedSExp} ->
        {tailReps, tailDomains, tailCodomains : RefinedSList} ->
        {auto headDomChecked : CheckedRefinement headDom} ->
        {auto headCodomChecked : CheckedRefinement headCodom} ->
        {auto headChecked :
          CheckedMorphism headRep headDom headCodom} ->
        {auto tailDomainsChecked : CheckedRefinementList tailDomains} ->
        {auto tailCodomainsChecked : CheckedRefinementList tailCodomains} ->
        {auto tailChecked :
          CheckedMorphismList tailReps tailDomains tailCodomains} ->
        InterpretedMorphismType
          headRep headDom headCodom {checked=headChecked} ->
        InterpretedMorphismList
          tailReps tailDomains tailCodomains {checked=tailChecked} ->
        InterpretedMorphismList
          (headRep :: tailReps)
          (headDom :: tailDomains)
          (headCodom :: tailCodomains)
          {domainsChecked=(
            CheckedRefinementListCons {head=headDom} {tail=tailDomains}
              headDomChecked tailDomainsChecked)}
          {codomainsChecked=(
            CheckedRefinementListCons {head=headCodom} {tail=tailCodomains}
              headCodomChecked tailCodomainsChecked)}
          {checked=(CheckedMorphismListCons {head=headRep} {tail=tailReps}
            {headDomain=headDom} {headCodomain=headCodom}
            {tailDomains} {tailCodomains} headChecked tailChecked)}

  public export
  interpretMorphismList : (representation, domains, codomains : RefinedSList) ->
    {auto domainsChecked : CheckedRefinementList domains} ->
    {auto codomainsChecked : CheckedRefinementList codomains} ->
    {auto checked : CheckedMorphismList representation domains codomains} ->
    InterpretedMorphismList representation domains codomains {checked}
  interpretMorphismList [] [] []
    {domainsChecked=Refl} {codomainsChecked=Refl} {checked=Refl} =
      EmptyInterpretedMorphismList
  interpretMorphismList (x :: l) (d :: ds) (c :: cs)
    {domainsChecked} {codomainsChecked} {checked} =
      ?interpretMorphismList_cons_hole
      {-
      InterpretedMorphismListCons
        {headDomChecked=(andLeft domainsChecked)}
        {headCodomChecked=(andLeft codomainsChecked)}
        {headChecked=(andLeft checked)}
        {tailDomainsChecked=(andRight domainsChecked)}
        {tailCodomainsChecked=(andRight codomainsChecked)}
        {tailChecked=(andRight checked)}
        (interpretMorphism x d c
          {domainChecked=(andLeft domainsChecked)}
          {codomainChecked=(andLeft codomainsChecked)}
          {checked=(andLeft checked)})
        (interpretMorphismList l ds cs
          {domainsChecked=(andRight domainsChecked)}
          {codomainsChecked=(andRight codomainsChecked)}
          {checked=(andRight checked)})
          -}

  {-
public export
Contract : {domain, codomain : Type} -> (f : domain -> codomain) -> Type
Contract {domain} {codomain} f =
  (P : domain -> Type ** Q : codomain -> Type ** (x : domain) -> P x -> Q (f x))

mutual
  public export
  interpretRefinedObject :
    {representation : RefinedSExp} -> RefinedObject representation -> Type
  interpretRefinedObject = interpretRefinedObject_hole
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
       interpretRefinedObject_mayberefinement_hole)
       -}
  {-

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
  interpretRefinedMorphism = interpretRefinedMorphism_hole
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
      interpretRefinedMorphism_compose_hole
      {-
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
      -}
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

      -}
