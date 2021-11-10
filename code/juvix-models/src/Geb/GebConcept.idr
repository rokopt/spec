module Geb.GebConcept

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.List
import public RefinedSExp.SExp
import public Data.SortedSet
import public Data.SortedMap
import public Data.DPair
import public Geb.GebAtom
import Category.Composition

%default total

--------------------------------------------------------------------------------

mutual
  public export
  data GebConceptRepresentation : Type where
    GebConceptCategoryRepresentation :
      GebCategoryRepresentation ->
      GebConceptRepresentation
    GebConceptObjectRepresentation :
      GebObjectRepresentation ->
      GebCategoryRepresentation ->
      GebConceptRepresentation
    GebConceptMorphismRepresentation:
      GebMorphismRepresentation ->
      GebCategoryRepresentation ->
      GebObjectRepresentation -> GebObjectRepresentation ->
      GebConceptRepresentation

  public export
  data GebCategoryRepresentation : Type where
    GebSelfRepresentation : GebCategoryRepresentation

  public export
  data GebObjectRepresentation : Type where

  public export
  data GebMorphismRepresentation : Type where

--------------------------------------------------------------------------------

public export
record GebConceptRepresentationFunctor where
  constructor GebConceptRepresentationMaps
  GebCategoryRepresentationMap :
    GebCategoryRepresentation -> GebCategoryRepresentation
  GebObjectRepresentationMap :
    GebObjectRepresentation -> GebObjectRepresentation
  GebMorphismRepresentationMap :
    GebMorphismRepresentation -> GebMorphismRepresentation

--------------------------------------------------------------------------------

mutual
  public export
  gebConceptRepToSExp : GebConceptRepresentation -> GebSExp
  gebConceptRepToSExp (GebConceptCategoryRepresentation catRep) =
    gebCategoryRepToSExp catRep
  gebConceptRepToSExp (GebConceptObjectRepresentation objRep catRep) =
    gebObjectRepToSExp objRep catRep
  gebConceptRepToSExp (GebConceptMorphismRepresentation
    morphismRep catRep domainRep codomainRep) =
      gebMorphismRepToSExp morphismRep catRep domainRep codomainRep

  public export
  gebCategoryRepToSExp : GebCategoryRepresentation -> GebSExp
  gebCategoryRepToSExp GebSelfRepresentation = $^ GAGeb

  public export
  gebObjectRepToSExp : GebObjectRepresentation -> GebCategoryRepresentation ->
    GebSExp
  gebObjectRepToSExp objRep catRep impossible

  public export
  gebMorphismRepToSExp : GebMorphismRepresentation ->
    GebCategoryRepresentation ->
    GebObjectRepresentation -> GebObjectRepresentation -> GebSExp
  gebMorphismRepToSExp morphismRep catRep domainRep codomainRep impossible

  public export
  gebConceptRepListToSList : List GebConceptRepresentation -> GebSList
  gebConceptRepListToSList [] = []
  gebConceptRepListToSList (rep :: reps) =
    gebConceptRepToSExp rep :: gebConceptRepListToSList reps

public export
gebExpToConceptRepCertified :
  ((x : GebSExp) -> Maybe
    (rep : GebConceptRepresentation **
      gebConceptRepToSExp rep = x),
   (l : GebSList) -> Maybe
    (reps: List GebConceptRepresentation **
      gebConceptRepListToSList reps = l))
gebExpToConceptRepCertified = sexpEliminators $ SExpEliminatorArgs
  (\a, l, maybeConcepts => case maybeConcepts of
    Just concepts => case a of
      GAGeb => case l of
        [] => Just $
          (GebConceptCategoryRepresentation GebSelfRepresentation ** Refl)
        _ :: _ => Nothing
      _ => Nothing
    Nothing => Nothing)
  (Just ([] ** Refl))
  (\_, _, maybeConcept, maybeConcepts => case (maybeConcept, maybeConcepts) of
    (Just (concept ** Refl), Just (concepts ** Refl)) =>
      Just $ ((concept :: concepts) ** Refl)
    _ => Nothing)

public export
gebSExpToConceptRep : GebSExp -> Maybe GebConceptRepresentation
gebSExpToConceptRep x = case (fst gebExpToConceptRepCertified x) of
  Just (rep ** _) => Just rep
  Nothing => Nothing

public export
gebSListToConceptRepList : GebSList -> Maybe (List GebConceptRepresentation)
gebSListToConceptRepList l = case (snd gebExpToConceptRepCertified l) of
  Just (reps ** _) => Just reps
  Nothing => Nothing

public export
gebSExpToConceptRepToSExp_correct :
  (x : GebSExp) -> (rep : GebConceptRepresentation) ->
  gebSExpToConceptRep x = Just rep -> gebConceptRepToSExp rep = x
gebSExpToConceptRepToSExp_correct x rep eq with
  (fst gebExpToConceptRepCertified x) proof p
    gebSExpToConceptRepToSExp_correct _ _ eq |
      Just (_ ** correct) = case eq of Refl => correct
    gebSExpToConceptRepToSExp_correct x rep eq |
      Nothing = case eq of Refl impossible

public export
gebSListToConceptRepListToSList_correct :
  (l : GebSList) -> (reps : List GebConceptRepresentation) ->
  gebSListToConceptRepList l = Just reps -> gebConceptRepListToSList reps = l
gebSListToConceptRepListToSList_correct l reps eq with
  (snd gebExpToConceptRepCertified l) proof p
    gebSListToConceptRepListToSList_correct l reps eq |
      Just (_ ** correct) = case eq of Refl => correct
    gebSListToConceptRepListToSList_correct l reps eq |
      Nothing = case eq of Refl impossible

mutual
  public export
  gebConceptRepToSExpToConceptRep_correct : (rep : GebConceptRepresentation) ->
    gebSExpToConceptRep (gebConceptRepToSExp rep) = Just rep

  public export
  gebConceptRepListToSListToConceptRepList_correct :
    (reps : List GebConceptRepresentation) ->
    gebSListToConceptRepList (gebConceptRepListToSList reps) = Just reps

--------------------------------------------------------------------------------

public export
Show GebConceptRepresentation where
  show = show . gebConceptRepToSExp

public export
Eq GebConceptRepresentation where
  rep == rep' = gebConceptRepToSExp rep == gebConceptRepToSExp rep'

public export
DecEq GebConceptRepresentation where
  decEq =
    encodingDecEq
      gebConceptRepToSExp gebSExpToConceptRep
      gebConceptRepToSExpToConceptRep_correct decEq

public export
Ord GebConceptRepresentation where
  rep < rep' = gebConceptRepToSExp rep < gebConceptRepToSExp rep'

--------------------------------------------------------------------------------

mutual
  public export
  data GebConcept : GebConceptRepresentation -> Type
    where
      GebConceptCategory : {representation : GebCategoryRepresentation} ->
        GebCategory representation ->
        GebConcept (GebConceptCategoryRepresentation representation)
      GebConceptObject : {objRep : GebObjectRepresentation} ->
        {catRep : GebCategoryRepresentation} ->
        GebObject objRep catRep ->
        GebConcept (GebConceptObjectRepresentation objRep catRep)
      GebConceptMorphism : {morphismRep : GebMorphismRepresentation} ->
        {catRep : GebCategoryRepresentation} ->
        {domainRep, codomainRep : GebObjectRepresentation} ->
        GebMorphism morphismRep catRep domainRep codomainRep ->
        GebConcept (GebConceptMorphismRepresentation
          morphismRep catRepd domainRep codomainRep)

  public export
  data GebCategory : GebCategoryRepresentation -> Type
    where
      GebInGeb : GebCategory GebSelfRepresentation

  public export
  data GebObject : GebObjectRepresentation -> GebCategoryRepresentation -> Type
    where

  public export
  data GebMorphism : GebMorphismRepresentation -> GebCategoryRepresentation ->
    (domain, codomain : GebObjectRepresentation) -> Type
    where

--------------------------------------------------------------------------------

public export
record GebConceptFunctor
  (representationFunctor : GebConceptRepresentationFunctor) where
    constructor GebConceptMaps
    GebCategoryMap : (catRep : GebCategoryRepresentation) ->
      GebCategory catRep ->
      GebCategory (GebCategoryRepresentationMap representationFunctor catRep)
    GebObjectMap : (catRep : GebCategoryRepresentation) ->
      (category : GebCategory catRep) ->
      (objRep : GebObjectRepresentation) ->
      GebObject objRep catRep ->
      GebObject
        (GebObjectRepresentationMap representationFunctor objRep)
        (GebCategoryRepresentationMap representationFunctor catRep)
    GebMorphismMap : (catRep : GebCategoryRepresentation) ->
      (category : GebCategory catRep) ->
      (domainRep, codomainRep : GebObjectRepresentation) ->
      (domain : GebObject domainRep catRep) ->
      (codomain : GebObject codomainRep catRep) ->
      (morphimRep : GebMorphismRepresentation) ->
      GebMorphism morphismRep catRep domainRep codomainRep ->
      GebMorphism
        (GebMorphismRepresentationMap representationFunctor morphismRep)
        (GebCategoryRepresentationMap representationFunctor catRep)
        (GebObjectRepresentationMap representationFunctor domainRep)
        (GebObjectRepresentationMap representationFunctor codomainRep)

--------------------------------------------------------------------------------

mutual
  public export
  checkGebConceptRepresentation : (representation : GebConceptRepresentation) ->
    Maybe (GebConcept representation)
  checkGebConceptRepresentation
    (GebConceptCategoryRepresentation GebSelfRepresentation) =
      Just $ GebConceptCategory GebInGeb
  checkGebConceptRepresentation (GebConceptObjectRepresentation _ _)
    impossible
  checkGebConceptRepresentation (GebConceptMorphismRepresentation _ _ _ _)
    impossible

mutual
  public export
  checkGebConceptRepresentation_complete :
    {representation : GebConceptRepresentation} ->
    (concept : GebConcept representation) ->
    checkGebConceptRepresentation representation = Just concept
  checkGebConceptRepresentation_complete (GebConceptCategory GebInGeb) = Refl
  checkGebConceptRepresentation_complete (GebConceptObject _) impossible
  checkGebConceptRepresentation_complete (GebConceptMorphism _) impossible

mutual
  public export
  gebConcept_uniquelyDeterminedByRepresentation :
    {representation : GebConceptRepresentation} ->
    (concept, concept' : GebConcept representation) ->
    concept = concept'
  gebConcept_uniquelyDeterminedByRepresentation
    (GebConceptCategory GebInGeb) (GebConceptCategory GebInGeb) = Refl
  gebConcept_uniquelyDeterminedByRepresentation
    (GebConceptObject _) _ impossible
  gebConcept_uniquelyDeterminedByRepresentation
    (GebConceptMorphism _) impossible

--------------------------------------------------------------------------------

public export
gebObjectCategory : {objRep : GebObjectRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  GebObject objRep catRep ->
  GebCategory catRep
gebObjectCategory object impossible

public export
gebMorphismCategory : {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  GebMorphism morphismRep catRep domainRep codomainRep ->
  GebCategory catRep
gebMorphismCategory morphism impossible

public export
gebMorphismDomain : {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  GebMorphism morphismRep catRep domainRep codomainRep ->
  GebObject domainRep catRep
gebMorphismDomain morphism impossible

public export
gebMorphismCodomain : {morphismRep : GebMorphismRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  {domainRep, codomainRep : GebObjectRepresentation} ->
  GebMorphism morphismRep catRep domainRep codomainRep ->
  GebObject codomainRep catRep
gebMorphismCodomain morphism impossible

--------------------------------------------------------------------------------

mutual
  public export
  interpretGebConceptType : {conceptRep : GebConceptRepresentation} ->
    GebConcept conceptRep ->
    Type
  interpretGebConceptType (GebConceptCategory _) = Type
  interpretGebConceptType (GebConceptObject _) = Type
  interpretGebConceptType (GebConceptMorphism morphism) =
    (rewrite
      sym (interpretGebCategory_isUniverse (gebMorphismCategory morphism)) in
     interpretGebObject (gebMorphismCategory morphism)
      (gebMorphismDomain morphism)) ->
    (rewrite
      sym (interpretGebCategory_isUniverse (gebMorphismCategory morphism)) in
     interpretGebObject (gebMorphismCategory morphism)
      (gebMorphismCodomain morphism))

  public export
  interpretGebCategory : {catRep : GebCategoryRepresentation} ->
    -- This should really be "Universe", but Idris doesn't have that as a type.
    GebCategory catRep ->
    Type
  interpretGebCategory _ = Type

  public export
  interpretGebCategory_isUniverse : {catRep : GebCategoryRepresentation} ->
    (category : GebCategory catRep) ->
    interpretGebCategory category = Type
  interpretGebCategory_isUniverse _ = Refl

  public export
  interpretGebConcept : {conceptRep : GebConceptRepresentation} ->
    (concept : GebConcept conceptRep) ->
    interpretGebConceptType concept
  interpretGebConcept (GebConceptCategory category) =
    interpretGebCategory category
  interpretGebConcept (GebConceptObject object) =
    interpretGebObject (gebObjectCategory object) object
  interpretGebConcept (GebConceptMorphism morphism) =
    interpretGebMorphism
      (gebMorphismCategory morphism)
      (gebMorphismDomain morphism)
      (gebMorphismCodomain morphism)
      morphism

  public export
  interpretGebObject : {objRep : GebObjectRepresentation} ->
    {catRep : GebCategoryRepresentation} ->
    (category : GebCategory catRep) ->
    GebObject objRep catRep ->
    interpretGebCategory category
  interpretGebObject _ impossible

  public export
  interpretGebMorphism : {morphismRep : GebMorphismRepresentation} ->
    {catRep : GebCategoryRepresentation} ->
    {domainRep, codomainRep : GebObjectRepresentation} ->
    (category : GebCategory catRep) ->
    (domain : GebObject domainRep catRep) ->
    (codomain : GebObject codomainRep catRep) ->
    GebMorphism morphismRep catRep domainRep codomainRep ->
    (rewrite sym (interpretGebCategory_isUniverse category) in
     interpretGebObject category domain) ->
    (rewrite sym (interpretGebCategory_isUniverse category) in
     interpretGebObject category codomain)
  interpretGebMorphism _ impossible

--------------------------------------------------------------------------------
