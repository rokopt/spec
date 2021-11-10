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

mutual
  public export
  gebConceptRepToSExp : GebConceptRepresentation -> GebSExp
  gebConceptRepToSExp = ?gebConceptRepToSExp_hole

  public export
  gebConceptRepListToSList : List GebConceptRepresentation -> GebSList
  gebConceptRepListToSList = ?gebConceptRepListToSList_hole

public export
gebExpToConceptRep :
  (GebSExp -> Maybe GebConceptRepresentation,
   GebSList -> Maybe (List GebConceptRepresentation))
gebExpToConceptRep = sexpEliminators $ SExpEliminatorArgs
  (?gebExpToConceptRep_hole_expElim)
  (?gebExpToConceptRep_hole_nilElim)
  (?gebExpToConceptRep_hole_consElim)

public export
gebSExpToConceptRep : GebSExp -> Maybe GebConceptRepresentation
gebSExpToConceptRep = fst gebExpToConceptRep

public export
gebSListToConceptRepList : GebSList -> Maybe (List GebConceptRepresentation)
gebSListToConceptRepList = snd gebExpToConceptRep

mutual
  public export
  gebConceptRepToSExpToConceptRep_correct : (rep : GebConceptRepresentation) ->
    gebSExpToConceptRep (gebConceptRepToSExp rep) = Just rep

  public export
  gebConceptRepListToSListToConceptRepList_correct :
    (reps : List GebConceptRepresentation) ->
    gebSListToConceptRepList (gebConceptRepListToSList reps) = Just reps

public export
gebExpToConceptRepToExp_correct :
  ((x : GebSExp) -> (rep : GebConceptRepresentation) ->
   gebSExpToConceptRep x = Just rep -> gebConceptRepToSExp rep = x,
   (l: GebSList) -> (reps : List GebConceptRepresentation) ->
   gebSListToConceptRepList l = Just reps -> gebConceptRepListToSList reps = l)
gebExpToConceptRepToExp_correct = sexpEliminators $ SExpEliminatorArgs
  (?gebExpToConceptRepToExp_correct_hole_expElim)
  (?gebExpToConceptRepToExp_correct_hole_nilElim)
  (?gebExpToConceptRepToExp_correct_hole_consElim)

public export
gebSExpToConceptRepToSExp_correct :
  (x : GebSExp) -> (rep : GebConceptRepresentation) ->
  gebSExpToConceptRep x = Just rep -> gebConceptRepToSExp rep = x
gebSExpToConceptRepToSExp_correct = fst gebExpToConceptRepToExp_correct

public export
gebSListToConceptRepListToSList_correct :
  (l : GebSList) -> (reps : List GebConceptRepresentation) ->
  gebSListToConceptRepList l = Just reps -> gebConceptRepListToSList reps = l
gebSListToConceptRepListToSList_correct = snd gebExpToConceptRepToExp_correct

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

mutual
  public export
  typecheckGebConcept : (representation : GebConceptRepresentation) ->
    Maybe (GebConcept representation)
  typecheckGebConcept = ?typecheckGebConcept_hole

mutual
  public export
  typecheckGebConcept_complete : {representation : GebConceptRepresentation} ->
    (concept : GebConcept representation) ->
    typecheckGebConcept representation = Just concept
  typecheckGebConcept_complete = ?typecheckGebConcept_complete_hole

--------------------------------------------------------------------------------
