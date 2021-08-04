module RefinedSExp.New.RefinedSExp

import public RefinedSExp.New.RefinedList
import public RefinedSExp.New.SExp
import public Library.Decidability

%default total

public export
record SExpAllOrExistsSig {0 atom : Type} (f : Type -> Type)
  (sl, sr : SExpPred atom) where
    constructor SExpAllOrExistsArgs
    atomElim : (a : atom) ->
      f (DepEither sl sr ($^ a))
    listElim : (l : SList atom) ->
      f (SListForAll sl l -> DepEither sl sr ($| l))

public export
SExpAllOrExistsAtomElimToEliminatorAtomElim : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  ((a : atom) -> f (DepEither sl sr ($^ a))) ->
  ((a : atom) -> f (SExpAllLeftOrExistsRight sl sr ($^ a)))
SExpAllOrExistsAtomElimToEliminatorAtomElim {f} {sl} {sr} inAtomElim a =
  applyEitherElim (pure Left) (pure (\r => Right (r, []))) (inAtomElim a)

public export
SExpAllOrExistsListElimToEliminatorListElim : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  ((l : SList atom) -> f (SListForAll sl l -> DepEither sl sr ($| l))) ->
  ((l : SList atom) ->
   f (SListAllLeftOrExistsRight sl sr l) ->
   f (SExpAllLeftOrExistsRight sl sr ($| l)))
SExpAllOrExistsListElimToEliminatorListElim {f} {sl} {sr} inListElim l =
  ?SExpAllOrExistsListElimToEliminatorListElim_hole

public export
SExpAllOrExistsEliminatorConsElim : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  ((x : SExp atom) -> (l : SList atom) ->
   f (SExpAllLeftOrExistsRight sl sr x) ->
   f (SListAllLeftOrExistsRight sl sr l) ->
   f (SListAllLeftOrExistsRight sl sr (x :: l)))
SExpAllOrExistsEliminatorConsElim {f} {sl} {sr} x l fx fl =
  ?SExpAllOrExistsEliminatorConsElim_hole

public export
SExpAllOrExistsSigToEliminatorSig : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} f sl sr ->
  SExpEliminatorSig
    (f . SExpAllLeftOrExistsRight sl sr, f . SListAllLeftOrExistsRight sl sr)
SExpAllOrExistsSigToEliminatorSig {f} {isApplicative} signature =
  SExpEliminatorArgs
    (SExpAllOrExistsAtomElimToEliminatorAtomElim
      {f} {sl} {sr} {isApplicative} (atomElim signature))
    (SExpAllOrExistsListElimToEliminatorListElim
      {f} {sl} {sr} {isApplicative} (listElim signature))
    (pure (Left ()))
    (SExpAllOrExistsEliminatorConsElim {f} {sl} {sr} {isApplicative})

public export
sexpAllOrExistsEliminators : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} f sl sr ->
  SPredPis
    (f . SExpAllLeftOrExistsRight sl sr, f . SListAllLeftOrExistsRight sl sr)
sexpAllOrExistsEliminators {isApplicative} =
  sexpEliminators . SExpAllOrExistsSigToEliminatorSig {isApplicative}
