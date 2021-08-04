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
  map
    (\eithers => case eithers of
      (Left xAllLeft, Left lAllLeft) => Left (xAllLeft, lAllLeft)
      (Left xAllLeft, Right rExistsRight) =>
        Right (slistExistsSomeShift {sr} rExistsRight)
      (Right xExistsRight, Left lAllLeft) =>
        Right ?SExpAllOrExistsEliminatorConsElim_hole_right_left
      (Right xExistsRight, Right rExistsRight) =>
        Right ?SExpAllOrExistsEliminatorConsElim_hole_right_right
    {-
    (Left sForAll, Left lForAll) => Left (sForAll, lForAll)
    (Left sForAll, Right lExists) => Right (slistExistsShift lExists)
    (Right sExists, Left lForAll) => Right (sexpExistsList sExists)
    (Right sExists, Right lExists) => Right (slistExistsMerge sExists lExists))
    -}
    )
    (applyPair fx fl)

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

public export
sexpAllOrExistsEliminator : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} f sl sr ->
  ((x : SExp atom) -> f (SExpAllLeftOrExistsRight sl sr x))
sexpAllOrExistsEliminator {isApplicative} =
  fst . sexpAllOrExistsEliminators {isApplicative}

public export
slistAllOrExistsEliminator : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} f sl sr ->
  ((l : SList atom) -> f (SListAllLeftOrExistsRight sl sr l))
slistAllOrExistsEliminator {isApplicative} =
  snd . sexpAllOrExistsEliminators {isApplicative}

public export
SExpAllOrExistsMetaPreds : {atom : Type} ->
  (f : Type -> Type) -> (sl, sr : SExpPred atom) -> Type
SExpAllOrExistsMetaPreds f sl sr =
  ((x : SExp atom) -> f (SExpAllLeftOrExistsRight sl sr x) -> Type,
   (l : SList atom) -> f (SListAllLeftOrExistsRight sl sr l) -> Type)

public export
record SExpAllOrExistsMetaEliminatorSig {0 atom : Type}
  {f : Type -> Type} {isApplicative : Applicative f}
  {sl, sr : SExpPred atom}
  (signature : SExpAllOrExistsSig {atom} f sl sr)
  (smps : SExpAllOrExistsMetaPreds f sl sr)
  where
    constructor SExpAllOrExistsMetaEliminatorArgs

SExpAllOrExistsMetaEliminatorSigToMetaEliminatorSig : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  {signature : SExpAllOrExistsSig {atom} f sl sr} ->
  {smps : SExpAllOrExistsMetaPreds f sl sr} ->
  SExpAllOrExistsMetaEliminatorSig {isApplicative} signature smps ->
  SExpMetaEliminatorSig
    (SExpAllOrExistsSigToEliminatorSig {isApplicative} signature)
    smps
SExpAllOrExistsMetaEliminatorSigToMetaEliminatorSig metaSig =
  ?SExpAllOrExistsMetaEliminatorSigToMetaEliminatorSig_hole

public export
sexpAllOrExistsMetaEliminators : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  {signature : SExpAllOrExistsSig {atom} f sl sr} ->
  {smps : SExpAllOrExistsMetaPreds f sl sr} ->
  SExpAllOrExistsMetaEliminatorSig {isApplicative} signature smps ->
  SExpSigPis (SExpAllOrExistsSigToEliminatorSig {isApplicative} signature) smps
sexpAllOrExistsMetaEliminators {isApplicative} =
  sexpMetaEliminators .
    SExpAllOrExistsMetaEliminatorSigToMetaEliminatorSig {isApplicative}

public export
SExpReturnsLeft : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  (signature : SExpAllOrExistsSig {atom} f sl sr) ->
  (x : SExp atom) -> f Type
SExpReturnsLeft {isApplicative} signature x =
  map IsLeft (sexpAllOrExistsEliminator {isApplicative} signature x)

public export
SListReturnsLeft : {0 atom : Type} ->
  {f : Type -> Type} -> {isApplicative : Applicative f} ->
  {sl, sr : SExpPred atom} ->
  (signature : SExpAllOrExistsSig {atom} f sl sr) ->
  (l : SList atom) -> f Type
SListReturnsLeft {isApplicative} signature l =
  map IsLeft (slistAllOrExistsEliminator {isApplicative} signature l)

public export
record SExpReturnsLeftEliminatorSig {0 atom : Type}
  {f : Type -> Type} {isApplicative : Applicative f}
  {sl, sr : SExpPred atom}
  (signature : SExpAllOrExistsSig {atom} f sl sr)
  where
    constructor SExpReturnsLeftEliminatorArgs
