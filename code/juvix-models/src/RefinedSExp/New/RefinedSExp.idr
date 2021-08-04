module RefinedSExp.New.RefinedSExp

import public RefinedSExp.New.RefinedList
import public RefinedSExp.New.SExp
import public Library.Decidability

%default total

{- XXX write a signature composer for this -}
public export
record SExpAllOrExistsSig {0 atom : Type}
  (sl, sr : SExpPred atom) where
    constructor SExpAllOrExistsArgs
    atomElim : (a : atom) -> DepEither sl sr ($^ a)
    listElim : (l : SList atom) -> SListForAll sl l -> DepEither sl sr ($| l)

public export
SExpAllOrExistsAtomElimToEliminatorAtomElim : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  ((a : atom) -> DepEither sl sr ($^ a)) ->
  (a : atom) ->
  SExpAllLeftOrExistsRight sl sr ($^ a)
SExpAllOrExistsAtomElimToEliminatorAtomElim {sl} {sr} inAtomElim a =
  case inAtomElim a of
    Left aLeft => Left aLeft
    Right aRight => Right (aRight, [])

public export
SExpAllOrExistsListElimToEliminatorListElim : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  ((l : SList atom) -> SListForAll sl l -> DepEither sl sr ($| l)) ->
  (l : SList atom) ->
  SListAllLeftOrExistsRight sl sr l ->
  SExpAllLeftOrExistsRight sl sr ($| l)
SExpAllOrExistsListElimToEliminatorListElim {sl} {sr} inListElim l spl =
  ?SExpAllOrExistsListElimToEliminatorListElim_hole

public export
SExpAllOrExistsEliminatorConsElim : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  ((x : SExp atom) -> (l : SList atom) ->
   SExpAllLeftOrExistsRight sl sr x ->
   SListAllLeftOrExistsRight sl sr l ->
   SListAllLeftOrExistsRight sl sr (x :: l))
SExpAllOrExistsEliminatorConsElim {sl} {sr} x l spx lpl =
  case (spx, lpl) of
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

public export
SExpAllOrExistsSigToEliminatorSig : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} sl sr ->
  SExpEliminatorSig
    (SExpAllLeftOrExistsRight sl sr, SListAllLeftOrExistsRight sl sr)
SExpAllOrExistsSigToEliminatorSig {sl} {sr} signature =
  SExpEliminatorArgs
    (SExpAllOrExistsAtomElimToEliminatorAtomElim {sl} {sr} (atomElim signature))
    (SExpAllOrExistsListElimToEliminatorListElim {sl} {sr} (listElim signature))
    (Left ())
    (SExpAllOrExistsEliminatorConsElim {sl} {sr})

{- XXX write aliases for these return types -}
public export
sexpAllOrExistsEliminators : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} sl sr ->
  ((x : SExp atom) -> SExpAllLeftOrExistsRight sl sr x,
   (l : SList atom) -> SListAllLeftOrExistsRight sl sr l)
sexpAllOrExistsEliminators =
  sexpEliminators . SExpAllOrExistsSigToEliminatorSig

public export
sexpAllOrExistsEliminator : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} sl sr ->
  ((x : SExp atom) -> SExpAllLeftOrExistsRight sl sr x)
sexpAllOrExistsEliminator = fst . sexpAllOrExistsEliminators

public export
slistAllOrExistsEliminator : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  SExpAllOrExistsSig {atom} sl sr ->
  ((l : SList atom) -> SListAllLeftOrExistsRight sl sr l)
slistAllOrExistsEliminator = snd . sexpAllOrExistsEliminators

{- XXX write aliases for each half of these return types -}
public export
SExpAllOrExistsMetaPreds : {atom : Type} ->
  (sl, sr : SExpPred atom) -> Type
SExpAllOrExistsMetaPreds sl sr =
  ((x : SExp atom) -> SExpAllLeftOrExistsRight sl sr x -> Type,
   (l : SList atom) -> SListAllLeftOrExistsRight sl sr l -> Type)

{- XXX write aliases for these composed return types -}
public export
sexpAllOrExistsMetaEliminators : {atom : Type} ->
  {sl, sr : SExpPred atom} ->
  {signature : SExpAllOrExistsSig {atom} sl sr} ->
  {smps : SExpAllOrExistsMetaPreds sl sr} ->
  SExpMetaEliminatorSig smps (SExpAllOrExistsSigToEliminatorSig signature) ->
  SExpSigPis smps (SExpAllOrExistsSigToEliminatorSig signature)
sexpAllOrExistsMetaEliminators =
  sexpMetaEliminators

{- XXX write a mapped-through-functor version of this -}
public export
SExpReturnsLeft : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  (signature : SExpAllOrExistsSig {atom} sl sr) ->
  SExp atom -> Type
SExpReturnsLeft signature x = IsLeft (sexpAllOrExistsEliminator signature x)

{- XXX write a mapped-through-functor version of this -}
public export
SListReturnsLeft : {0 atom : Type} ->
  {sl, sr : SExpPred atom} ->
  (signature : SExpAllOrExistsSig {atom} sl sr) ->
  SList atom -> Type
SListReturnsLeft signature l = IsLeft (slistAllOrExistsEliminator signature l)

-- XXX depdendent transformers; dependently-typed programming languages;
-- elimination of refined sexps to dependently-typed programming languages;
-- elimination of refined sexps to dependently-typed programming languages;
-- parameterized (on other dependently-typed programming languages)
-- dependently-typed programming languages; elimination of refined sexps
-- to parameterized dependently-typed programming languages; elimination
-- of refined sexps to transformations between dependently-typed programming
-- languages; refined sexps _as_ a dependently-typed programming language;
-- dependently-typed metaprogramming
