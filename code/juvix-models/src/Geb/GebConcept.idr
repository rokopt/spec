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
    GAConceptCategory $*** gebCategoryRepToSExp catRep
  gebConceptRepToSExp (GebConceptObjectRepresentation objRep catRep) =
    GAConceptObject $* [gebObjectRepToSExp objRep, gebCategoryRepToSExp catRep]
  gebConceptRepToSExp (GebConceptMorphismRepresentation
    morphismRep catRep domainRep codomainRep) =
      GAConceptMorphism $*
        [gebMorphismRepToSExp morphismRep,
         gebCategoryRepToSExp catRep,
         gebObjectRepToSExp domainRep,
         gebObjectRepToSExp codomainRep]

  public export
  gebCategoryRepToSExp : GebCategoryRepresentation -> GebSExp
  gebCategoryRepToSExp GebSelfRepresentation = $^ GAGeb

  public export
  gebObjectRepToSExp : GebObjectRepresentation -> GebSExp
  gebObjectRepToSExp (GebReflectiveObjectRepresentation catRep) =
    GAReflectiveObject $*** gebCategoryRepToSExp catRep

  public export
  gebMorphismRepToSExp : GebMorphismRepresentation -> GebSExp
  gebMorphismRepToSExp morphismRep impossible

--------------------------------------------------------------------------------

mutual
  public export
  gebSExpToCategoryRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebCategoryRepresentation ** gebCategoryRepToSExp rep = x)
  gebSExpToCategoryRepCertified (a $* l) =
    case decEq a GAGeb of
      Yes Refl => case decEq l [] of
        Yes Refl => Yes $ (GebSelfRepresentation ** Refl)
        No isNotNil => No $ \p => case p of
          (GebSelfRepresentation ** repIsGeb) => case repIsGeb of
            Refl => void $ isNotNil Refl
      No isNotGeb => No $ \p => case p of
        (GebSelfRepresentation ** repIsGeb) => case repIsGeb of
          Refl => void $ isNotGeb Refl

  public export
  gebCategoryRepToSExpToCategoryRepCertified_correct :
    (rep : GebCategoryRepresentation) ->
    gebSExpToCategoryRepCertified (gebCategoryRepToSExp rep) = Yes (rep ** Refl)
  gebCategoryRepToSExpToCategoryRepCertified_correct GebSelfRepresentation =
    rewrite decEqRefl decEq GAGeb in Refl

  public export
  gebSExpToCategoryRep : GebSExp -> Maybe GebCategoryRepresentation
  gebSExpToCategoryRep = decMapToMaybe gebSExpToCategoryRepCertified

  public export
  gebCategoryRepToSExpToCategoryRep_correct :
    (rep : GebCategoryRepresentation) ->
    gebSExpToCategoryRep (gebCategoryRepToSExp rep) = Just rep
  gebCategoryRepToSExpToCategoryRep_correct rep =
    rewrite gebCategoryRepToSExpToCategoryRepCertified_correct rep in
    Refl

  public export
  gebSExpToCategoryRepToSExp_correct :
    (x : GebSExp) -> (rep : GebCategoryRepresentation) ->
    gebSExpToCategoryRep x = Just rep -> gebCategoryRepToSExp rep = x
  gebSExpToCategoryRepToSExp_correct =
    decMapToMaybe_correct gebSExpToCategoryRepCertified

  public export
  gebCategoryRepToSExp_injective : (rep, rep' : GebCategoryRepresentation) ->
    gebCategoryRepToSExp rep = gebCategoryRepToSExp rep' ->
    rep = rep'
  gebCategoryRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToCategoryRepCertified
      gebCategoryRepToSExpToCategoryRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToObjectRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebObjectRepresentation ** gebObjectRepToSExp rep = x)
  gebSExpToObjectRepCertified (a $* l) =
    case decEq a GAReflectiveObject of
      Yes Refl => case l of
        [] => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
          ((GebConceptObjectRepresentation _ _) ** Refl) impossible
          ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
        [cat] => case gebSExpToCategoryRepCertified cat of
          Yes (catRep ** Refl) =>
            Yes (GebReflectiveObjectRepresentation catRep ** Refl)
          No notCategory => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ((GebConceptObjectRepresentation _ _) ** Refl) impossible
            ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
        (_ :: _ :: _) => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
          ((GebConceptObjectRepresentation _ _) ** Refl) impossible
          ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
      No isNotReflective => No $ \p => case p of
        (GebReflectiveObjectRepresentation category ** repIsReflective) =>
          case repIsReflective of Refl => void $ isNotReflective Refl

  public export
  gebObjectRepToSExpToObjectRepCertified_correct :
    (rep : GebObjectRepresentation) ->
    gebSExpToObjectRepCertified (gebObjectRepToSExp rep) = Yes (rep ** Refl)
  gebObjectRepToSExpToObjectRepCertified_correct
    (GebReflectiveObjectRepresentation catRep) =
      rewrite decEqRefl decEq GAReflectiveObject in
      rewrite gebCategoryRepToSExpToCategoryRepCertified_correct catRep in
      Refl

  public export
  gebSExpToObjectRep : GebSExp -> Maybe GebObjectRepresentation
  gebSExpToObjectRep = decMapToMaybe gebSExpToObjectRepCertified

  public export
  gebObjectRepToSExpToObjectRep_correct :
    (rep : GebObjectRepresentation) ->
    gebSExpToObjectRep (gebObjectRepToSExp rep) = Just rep
  gebObjectRepToSExpToObjectRep_correct rep =
    rewrite gebObjectRepToSExpToObjectRepCertified_correct rep in
    Refl

  public export
  gebSExpToObjectRepToSExp_correct :
    (x : GebSExp) -> (rep : GebObjectRepresentation) ->
    gebSExpToObjectRep x = Just rep -> gebObjectRepToSExp rep = x
  gebSExpToObjectRepToSExp_correct =
    decMapToMaybe_correct gebSExpToObjectRepCertified

  public export
  gebObjectRepToSExp_injective : (rep, rep' : GebObjectRepresentation) ->
    gebObjectRepToSExp rep = gebObjectRepToSExp rep' ->
    rep = rep'
  gebObjectRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToObjectRepCertified
      gebObjectRepToSExpToObjectRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToMorphismRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebMorphismRepresentation ** gebMorphismRepToSExp rep = x)
  gebSExpToMorphismRepCertified (a $* l) = No $ \p => case p of
    ((GebConceptCategoryRepresentation _) ** Refl) impossible
    ((GebConceptObjectRepresentation _ _) ** Refl) impossible
    ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible

  public export
  gebMorphismRepToSExpToMorphismRepCertified_correct :
    (rep : GebMorphismRepresentation) ->
    gebSExpToMorphismRepCertified (gebMorphismRepToSExp rep) = Yes (rep ** Refl)
  gebMorphismRepToSExpToMorphismRepCertified_correct _ impossible

  public export
  gebSExpToMorphismRep : GebSExp -> Maybe GebMorphismRepresentation
  gebSExpToMorphismRep = decMapToMaybe gebSExpToMorphismRepCertified

  public export
  gebMorphismRepToSExpToMorphismRep_correct :
    (rep : GebMorphismRepresentation) ->
    gebSExpToMorphismRep (gebMorphismRepToSExp rep) = Just rep
  gebMorphismRepToSExpToMorphismRep_correct rep =
    rewrite gebMorphismRepToSExpToMorphismRepCertified_correct rep in
    Refl

  public export
  gebSExpToMorphismRepToSExp_correct :
    (x : GebSExp) -> (rep : GebMorphismRepresentation) ->
    gebSExpToMorphismRep x = Just rep -> gebMorphismRepToSExp rep = x
  gebSExpToMorphismRepToSExp_correct =
    decMapToMaybe_correct gebSExpToMorphismRepCertified

  public export
  gebMorphismRepToSExp_injective : (rep, rep' : GebMorphismRepresentation) ->
    gebMorphismRepToSExp rep = gebMorphismRepToSExp rep' ->
    rep = rep'
  gebMorphismRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToMorphismRepCertified
      gebMorphismRepToSExpToMorphismRep_correct

--------------------------------------------------------------------------------

  public export
  gebSExpToConceptRepCertified :
    (x : GebSExp) ->
    Dec (rep : GebConceptRepresentation ** gebConceptRepToSExp rep = x)
  gebSExpToConceptRepCertified (a $* l) =
    case decEq a GAConceptCategory of
      Yes Refl => case l of
        [] => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
          ((GebConceptObjectRepresentation _ _) ** Refl) impossible
          ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
        [category] => case gebSExpToCategoryRepCertified category of
          Yes (catRep ** Refl) =>
            Yes (GebConceptCategoryRepresentation catRep ** Refl)
          No notCategory => No $ \p => case p of
            ((GebConceptCategoryRepresentation catRep) ** correct) =>
              void $ notCategory (catRep **
                rewrite (fst (consInjective (sexpInjectiveList correct))) in
                Refl)
            ((GebConceptObjectRepresentation objRep catRep) ** Refl) impossible
            ((GebConceptMorphismRepresentation
              morphismRep catRep domainRep codomainRep) ** Refl) impossible
        (_ :: _ :: _) => No $ \p => case p of
          ((GebConceptCategoryRepresentation _) ** Refl) impossible
          ((GebConceptObjectRepresentation _ _) ** Refl) impossible
          ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
      No notCategory => case decEq a GAConceptObject of
        Yes Refl => case l of
          [] => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ((GebConceptObjectRepresentation _ _) ** Refl) impossible
            ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
          ([_]) => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ((GebConceptObjectRepresentation _ _) ** Refl) impossible
            ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
          (object :: category :: []) =>
            case gebSExpToObjectRepCertified object of
              Yes (objRep ** Refl) =>
                case gebSExpToCategoryRepCertified category of
                  Yes (catRep ** Refl) =>
                    Yes (GebConceptObjectRepresentation objRep catRep ** Refl)
                  No notCategory => No $ \p => case p of
                    ((GebConceptCategoryRepresentation _) ** Refl)
                      impossible
                    ((GebConceptObjectRepresentation objRep catRep) ** correct) =>
                      void $ notCategory (catRep **
                        fst (consInjective (snd
                           (consInjective (sexpInjectiveList correct)))))
                    ((GebConceptMorphismRepresentation _ _ _ _) ** Refl)
                      impossible
              No notObject => No $ \p => case p of
                ((GebConceptCategoryRepresentation _) ** Refl) impossible
                ((GebConceptObjectRepresentation objRep catRep) ** Refl) =>
                  notObject $ (objRep ** Refl)
                ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
          (_ :: _ :: _ :: _) => No $ \p => case p of
            ((GebConceptCategoryRepresentation _) ** Refl) impossible
            ((GebConceptObjectRepresentation _ _) ** Refl) impossible
            ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
        No notObject => case decEq a GAConceptMorphism of
          Yes Refl => case l of
            [] => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
              ((GebConceptObjectRepresentation _ _) ** Refl) impossible
              ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
            ([_]) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
              ((GebConceptObjectRepresentation _ _) ** Refl) impossible
              ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
            ([_, _]) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
              ((GebConceptObjectRepresentation _ _) ** Refl) impossible
              ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
            ([_, _, _]) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
              ((GebConceptObjectRepresentation _ _) ** Refl) impossible
              ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
            ([morphism, category, domain, codomain]) =>
              case (gebSExpToMorphismRepCertified morphism,
                    gebSExpToCategoryRepCertified category,
                    gebSExpToObjectRepCertified domain,
                    gebSExpToObjectRepCertified codomain) of
                (Yes (morphismRep ** Refl),
                 Yes (catRep ** Refl),
                 Yes (domainRep ** Refl),
                 Yes (codomainRep ** Refl)) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                  ((GebConceptObjectRepresentation _ _) ** Refl)
                    impossible
                  ((GebConceptMorphismRepresentation _ _ _ _) ** correct)
                    impossible
                (No notMorphism, _, _, _) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                  ((GebConceptObjectRepresentation _ _) ** Refl)
                    impossible
                  ((GebConceptMorphismRepresentation _ _ _ _) ** Refl)
                    impossible
                (_, No notCategory, _, _) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                  ((GebConceptObjectRepresentation _ _) ** Refl)
                    impossible
                  ((GebConceptMorphismRepresentation _ _ _ _) ** Refl)
                    impossible
                (_, _, No domainNotObject, _) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                  ((GebConceptObjectRepresentation _ _) ** Refl)
                    impossible
                  ((GebConceptMorphismRepresentation _ _ _ _) ** Refl)
                    impossible
                (_, _, _, No codomainNotObject) => No $ \p => case p of
                  ((GebConceptCategoryRepresentation _) ** Refl)
                    impossible
                  ((GebConceptObjectRepresentation _ _) ** Refl)
                    impossible
                  ((GebConceptMorphismRepresentation _ _ _ _) ** Refl)
                    impossible
            (_ :: _ :: _ :: _ :: _ :: _) => No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) impossible
              ((GebConceptObjectRepresentation _ _) ** Refl) impossible
              ((GebConceptMorphismRepresentation _ _ _ _) ** Refl) impossible
          No notMorphism =>
            No $ \p => case p of
              ((GebConceptCategoryRepresentation _) ** Refl) => notCategory Refl
              ((GebConceptObjectRepresentation _ _) ** Refl) => notObject Refl
              ((GebConceptMorphismRepresentation _ _ _ _) ** correct) =>
                notMorphism $ sym $ sexpInjectiveAtom correct

  public export
  gebConceptRepToSExpToConceptRepCertified_correct :
    (rep : GebConceptRepresentation) ->
    gebSExpToConceptRepCertified (gebConceptRepToSExp rep) = Yes (rep ** Refl)
  gebConceptRepToSExpToConceptRepCertified_correct
    (GebConceptCategoryRepresentation catRep) =
      rewrite decEqRefl decEq GAConceptCategory in
      rewrite gebCategoryRepToSExpToCategoryRepCertified_correct catRep in
      Refl
  gebConceptRepToSExpToConceptRepCertified_correct
    (GebConceptObjectRepresentation objectRep catRep) =
      ?gebConceptRepToSExpToConceptRepCertified_correct_hole_object
  gebConceptRepToSExpToConceptRepCertified_correct
    (GebConceptMorphismRepresentation
      morphismRep catRep domainRep codomainRep) =
        ?gebConceptRepToSExpToConceptRepCertified_correct_hole_morphism

  public export
  gebSExpToConceptRep : GebSExp -> Maybe GebConceptRepresentation
  gebSExpToConceptRep = decMapToMaybe gebSExpToConceptRepCertified

  public export
  gebConceptRepToSExpToConceptRep_correct :
    (rep : GebConceptRepresentation) ->
    gebSExpToConceptRep (gebConceptRepToSExp rep) = Just rep
  gebConceptRepToSExpToConceptRep_correct rep =
    rewrite gebConceptRepToSExpToConceptRepCertified_correct rep in
    Refl

  public export
  gebSExpToConceptRepToSExp_correct :
    (x : GebSExp) -> (rep : GebConceptRepresentation) ->
    gebSExpToConceptRep x = Just rep -> gebConceptRepToSExp rep = x
  gebSExpToConceptRepToSExp_correct =
    decMapToMaybe_correct gebSExpToConceptRepCertified

  public export
  gebConceptRepToSExp_injective : (rep, rep' : GebConceptRepresentation) ->
    gebConceptRepToSExp rep = gebConceptRepToSExp rep' ->
    rep = rep'
  gebConceptRepToSExp_injective =
    decMapToMaybe_injective
      gebSExpToConceptRepCertified
      gebConceptRepToSExpToConceptRep_correct

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
Show GebObjectRepresentation where
  show = show . gebObjectRepToSExp

public export
Eq GebObjectRepresentation where
  rep == rep' = gebObjectRepToSExp rep == gebObjectRepToSExp rep'

public export
DecEq GebObjectRepresentation where
  decEq =
    encodingDecEq
      gebObjectRepToSExp gebSExpToObjectRep
      gebObjectRepToSExpToObjectRep_correct decEq

public export
Ord GebObjectRepresentation where
  rep < rep' = gebObjectRepToSExp rep < gebObjectRepToSExp rep'

--------------------------------------------------------------------------------

public export
Show GebMorphismRepresentation where
  show = show . gebMorphismRepToSExp

public export
Eq GebMorphismRepresentation where
  rep == rep' = gebMorphismRepToSExp rep == gebMorphismRepToSExp rep'

public export
DecEq GebMorphismRepresentation where
  decEq =
    encodingDecEq
      gebMorphismRepToSExp gebSExpToMorphismRep
      gebMorphismRepToSExpToMorphismRep_correct decEq

public export
Ord GebMorphismRepresentation where
  rep < rep' = gebMorphismRepToSExp rep < gebMorphismRepToSExp rep'

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
          morphismRep catRep domainRep codomainRep)

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
  checkGebCategoryRepresentation :
    (representation : GebCategoryRepresentation) ->
    Dec (GebCategory representation)
  checkGebCategoryRepresentation GebSelfRepresentation = Yes GebInGeb

  public export
  checkGebConceptRepresentation : (representation : GebConceptRepresentation) ->
    Dec (GebConcept representation)
  checkGebConceptRepresentation
    (GebConceptCategoryRepresentation GebSelfRepresentation) =
      Yes $ GebConceptCategory GebInGeb
  checkGebConceptRepresentation (GebConceptObjectRepresentation
    (GebReflectiveObjectRepresentation catRep) catRep') =
      case decEq catRep catRep' of
        Yes Refl => case checkGebCategoryRepresentation catRep' of
          Yes category => Yes $ GebConceptObject $ GebReflectiveObject category
          No notCategory => No $ \concept => case concept of
            GebConceptObject (GebReflectiveObject category) =>
              void $ notCategory category
        No neq => No $ \concept => case concept of
          GebConceptObject (GebReflectiveObject category) => void $ neq Refl
  checkGebConceptRepresentation (GebConceptMorphismRepresentation _ _ _ _)
    impossible

mutual
  public export
  checkGebCategoryRepresentation_complete :
    {representation : GebCategoryRepresentation} ->
    (category : GebCategory representation) ->
    checkGebCategoryRepresentation representation = Yes category
  checkGebCategoryRepresentation_complete GebInGeb = Refl

  public export
  checkGebConceptRepresentation_complete :
    {representation : GebConceptRepresentation} ->
    (concept : GebConcept representation) ->
    checkGebConceptRepresentation representation = Yes concept
  checkGebConceptRepresentation_complete (GebConceptCategory GebInGeb) = Refl
  checkGebConceptRepresentation_complete (GebConceptObject
    (GebReflectiveObject {catRep} category)) =
      rewrite decEqRefl decEq catRep in
      rewrite checkGebCategoryRepresentation_complete category in
      Refl
  checkGebConceptRepresentation_complete (GebConceptMorphism _) impossible

public export
gebCategory_uniquelyDeterminedByRepresentation :
  {representation : GebCategoryRepresentation} ->
  (category, category' : GebCategory representation) ->
  category = category'
gebCategory_uniquelyDeterminedByRepresentation =
  depDecComplete_implies_unique
    checkGebCategoryRepresentation
    checkGebCategoryRepresentation_complete

public export
gebConcept_uniquelyDeterminedByRepresentation :
  {representation : GebConceptRepresentation} ->
  (category, category' : GebConcept representation) ->
  category = category'
gebConcept_uniquelyDeterminedByRepresentation =
  depDecComplete_implies_unique
    checkGebConceptRepresentation
    checkGebConceptRepresentation_complete

--------------------------------------------------------------------------------

public export
gebObjectCategory : {objRep : GebObjectRepresentation} ->
  {catRep : GebCategoryRepresentation} ->
  GebObject objRep catRep ->
  GebCategory catRep
gebObjectCategory (GebReflectiveObject category) = category

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
  interpretGebObject _ (GebReflectiveObject _) =
    GebConceptRepresentation

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
