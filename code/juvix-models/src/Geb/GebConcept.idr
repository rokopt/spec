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
