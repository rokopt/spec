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
    GebReflectiveObjectRepresentation :
      GebCategoryRepresentation -> GebObjectRepresentation

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
  gebObjectRepToSExp (GebReflectiveObjectRepresentation catRep) catRep' =
    GAReflectiveObject $*
      [gebCategoryRepToSExp catRep, gebCategoryRepToSExp catRep']

  public export
  gebMorphismRepToSExp : GebMorphismRepresentation ->
    GebCategoryRepresentation ->
    GebObjectRepresentation -> GebObjectRepresentation -> GebSExp
  gebMorphismRepToSExp morphismRep catRep domainRep codomainRep impossible

  public export
  gebCategoryRepListToSList : List GebCategoryRepresentation -> GebSList
  gebCategoryRepListToSList = map gebCategoryRepToSExp

  public export
  gebConceptRepListToSList : List GebConceptRepresentation -> GebSList
  gebConceptRepListToSList = map gebConceptRepToSExp

--------------------------------------------------------------------------------

public export
gebDecodeCategoryRep :
  (a : GebAtom) -> (l : GebSList) ->
  (categories : List GebCategoryRepresentation) ->
  map GebConcept.gebCategoryRepToSExp categories = l ->
  Maybe (rep : GebCategoryRepresentation ** gebCategoryRepToSExp rep = (a $* l))
gebDecodeCategoryRep = ?gebDecodeCategoryRep_hole

public export
gebSExpToCategoryRepCertified :
  (x : GebSExp) ->
  Maybe (rep : GebCategoryRepresentation ** gebCategoryRepToSExp rep = x)
gebSExpToCategoryRepCertified =
  decodeFromSExpCertified gebCategoryRepToSExp gebDecodeCategoryRep

public export
gebSExpToCategoryRep : GebSExp -> Maybe GebCategoryRepresentation
gebSExpToCategoryRep = decodeFromSExp gebCategoryRepToSExp gebDecodeCategoryRep

public export
gebSExpToCategoryRepToSExp_correct :
  (x : GebSExp) -> (rep : GebCategoryRepresentation) ->
  gebSExpToCategoryRep x = Just rep -> gebCategoryRepToSExp rep = x
gebSExpToCategoryRepToSExp_correct =
  sexpDecodeThenEncode_correct gebCategoryRepToSExp gebDecodeCategoryRep

public export
gebCategoryRepToSExpToCategoryRep_correct :
  (rep : GebCategoryRepresentation) ->
  gebSExpToCategoryRep (gebCategoryRepToSExp rep) = Just rep
gebCategoryRepToSExpToCategoryRep_correct =
  sexpEncodeThenDecode_correct gebCategoryRepToSExp gebDecodeCategoryRep

--------------------------------------------------------------------------------

public export
gebDecodeConceptRep :
  (a : GebAtom) -> (l : GebSList) ->
  (categories : List GebConceptRepresentation) ->
  map GebConcept.gebConceptRepToSExp categories = l ->
  Maybe (rep : GebConceptRepresentation ** gebConceptRepToSExp rep = (a $* l))
gebDecodeConceptRep = ?gebDecodeConceptRep_hole

public export
gebSExpToConceptRepCertified :
  (x : GebSExp) ->
  Maybe (rep : GebConceptRepresentation ** gebConceptRepToSExp rep = x)
gebSExpToConceptRepCertified =
  decodeFromSExpCertified gebConceptRepToSExp gebDecodeConceptRep

public export
gebSExpToConceptRep : GebSExp -> Maybe GebConceptRepresentation
gebSExpToConceptRep = decodeFromSExp gebConceptRepToSExp gebDecodeConceptRep

public export
gebSExpToConceptRepToSExp_correct :
  (x : GebSExp) -> (rep : GebConceptRepresentation) ->
  gebSExpToConceptRep x = Just rep -> gebConceptRepToSExp rep = x
gebSExpToConceptRepToSExp_correct =
  sexpDecodeThenEncode_correct gebConceptRepToSExp gebDecodeConceptRep

public export
gebConceptRepToSExpToConceptRep_correct :
  (rep : GebConceptRepresentation) ->
  gebSExpToConceptRep (gebConceptRepToSExp rep) = Just rep
gebConceptRepToSExpToConceptRep_correct =
  sexpEncodeThenDecode_correct gebConceptRepToSExp gebDecodeConceptRep

--------------------------------------------------------------------------------

public export
Show GebCategoryRepresentation where
  show = show . gebCategoryRepToSExp

public export
Eq GebCategoryRepresentation where
  rep == rep' = gebCategoryRepToSExp rep == gebCategoryRepToSExp rep'

public export
DecEq GebCategoryRepresentation where
  decEq =
    encodingDecEq
      gebCategoryRepToSExp gebSExpToCategoryRep
      gebCategoryRepToSExpToCategoryRep_correct decEq

public export
Ord GebCategoryRepresentation where
  rep < rep' = gebCategoryRepToSExp rep < gebCategoryRepToSExp rep'

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
      GebReflectiveObject : {catRep : GebCategoryRepresentation} ->
        GebCategory catRep ->
        GebObject (GebReflectiveObjectRepresentation catRep) catRep

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
  checkGebConceptRepresentation (GebConceptObjectRepresentation
    (GebReflectiveObjectRepresentation catRep) catRep') =
      case decEq catRep catRep' of
        Yes Refl => ?checkGebConceptRepresentation_hole
        No _ => Nothing
  checkGebConceptRepresentation (GebConceptMorphismRepresentation _ _ _ _)
    impossible

mutual
  public export
  checkGebConceptRepresentation_complete :
    {representation : GebConceptRepresentation} ->
    (concept : GebConcept representation) ->
    checkGebConceptRepresentation representation = Just concept
  checkGebConceptRepresentation_complete (GebConceptCategory GebInGeb) = Refl
  checkGebConceptRepresentation_complete (GebConceptObject
    (GebReflectiveObject category)) =
      ?checkGebConceptRepresentation_complete_hole
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
    (GebConceptObject (GebReflectiveObjectRepresentation catRep)) catRep
      impossible
  gebConcept_uniquelyDeterminedByRepresentation
    (GebConceptMorphism _) impossible

--------------------------------------------------------------------------------

public export
gebObjectCategory : {objRep : GebObjectRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  GebObject objRep catRep ->
  GebCategory catRep
gebObjectCategory (GebReflectiveObject category) = ?gebObjectCategory_hole

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
  interpretGebObject category' (GebReflectiveObject category) =
    ?interpretGetObject_hole

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
