module RefinedSExp.RefinedSExp

import public Library.Decidability
import public Data.Nat

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

%default total

-- | A StructExp/StructList is a form of S-expression for which identity is
-- | determined solely by structure -- there's no notion of a type of atom;
-- | there are simply anonymous "holes" where atoms might be, and any two
-- | holes might be either constrained to be equal or not.
mutual
  prefix 11 $<
  prefix 11 $|
  public export
  data StructExp : (holesInContext, holesInExpression : Nat) -> Type where
    -- | A reference to a hole in context constrains a hole to be equal to
    -- | the one it refers back to.
    ($<) : {holesInContext : Nat} ->
      Fin holesInContext ->
      StructExp holesInContext 0
    -- | A new hole might not be equal to any that comes before it in an
    -- | expression.
    ($>) : {holesInContext : Nat} ->
      StructExp holesInContext 1
    -- | A list may be viewed as an expression with the same context and
    -- | number of new holes.
    ($|) : {holesInContext, holesInList : Nat} ->
      StructList holesInContext holesInList ->
      StructExp holesInContext holesInList

  prefix 7 $-
  infixr 7 $:
  public export
  data StructList : (holesInContext, holesInList : Nat) -> Type where
    -- | An empty list contains no holes, and can be formed in any context.
    ($-) : {holesInContext : Nat} ->
      StructList holesInContext 0
    -- | A non-empty list's head introduces its new holes into the context
    -- | of the tail.  Thus it might be viewed as a form of telescope.
    ($:) : {holesInContext, holesInHead, holesInTail : Nat} ->
      StructExp holesInContext holesInHead ->
      StructList (holesInHead + holesInContext) holesInTail ->
      StructList holesInContext (holesInTail + holesInHead)

infixr 7 $:-
public export
($:-) : {holesInContext, holesInHead, holesInTail : Nat} ->
  StructExp holesInContext holesInHead ->
  StructExp (holesInHead + holesInContext) holesInTail ->
  StructList holesInContext (holesInTail + holesInHead)
h $:- t = h $: t $: ($-)

prefix 11 $<+
public export
($<+): {holesInContext : Nat} -> (m : Nat) ->
  {auto valid : m `LT` holesInContext} ->
  StructExp holesInContext 0
($<+) m {valid} = ($<) (natToFinCert valid)

public export
slength : {0 holesInContext, holesInList : Nat} ->
  StructList holesInContext holesInList -> Nat
slength ($-) = 0
slength (($:) h t) = S (slength t)

public export
sNth : {holesInListContext, holesInList : Nat} ->
  (l : StructList holesInListContext holesInList) ->
  (index : Nat) ->
  {auto indexValid : index `LT` (slength l)} ->
  (holesInContext : Nat ** holesInExp : Nat **
   StructExp holesInContext holesInExp)
sNth ($-) _ {indexValid} =
  void (succNotLTEzero indexValid)
sNth {holesInListContext} (($:) {holesInHead} h t) Z =
  (holesInListContext ** holesInHead ** h)
sNth {holesInListContext} (($:) h t) (S n) {indexValid} =
  sNth t n {indexValid=(fromLteSucc indexValid)}

public export
holesInNthContext : {holesInListContext, holesInList : Nat} ->
  (l : StructList holesInListContext holesInList) ->
  (index : Nat) -> {auto indexValid : index `LT` (slength l)} ->
  Nat
holesInNthContext l index = fst (sNth l index)

public export
holesInNthExp : {holesInListContext, holesInList : Nat} ->
  (l : StructList holesInListContext holesInList) ->
  (index : Nat) -> {auto indexValid : index `LT` (slength l)} ->
  Nat
holesInNthExp l index = fst (snd (sNth l index))

infix 11 $#
public export
($#) : {holesInListContext, holesInList : Nat} ->
  (l : StructList holesInListContext holesInList) ->
  (index : Nat) ->
  {auto indexValid : index `LT` (slength l)} ->
  StructExp
    (holesInNthContext {holesInListContext} {holesInList} l index {indexValid})
    (holesInNthExp {holesInListContext} {holesInList} l index {indexValid})
l $# index = snd (snd (sNth l index))

mutual
  public export
  data StructExpRefinement : (holesInContext, holesInExpression : Nat) ->
    Type where
      RefinementAsExp : {holesInContext, holesInList : Nat} ->
        StructListRefinement holesInContext holesInList ->
        StructExpRefinement holesInContext holesInList

  public export
  data StructListRefinement : (holesInContext, holesInList : Nat) ->
    Type where
      Telescope : {holesInContext, holesInHead, holesInTail : Nat} ->
        StructExpRefinement holesInContext holesInHead ->
        StructListRefinement (holesInHead + holesInContext) holesInTail ->
        StructListRefinement holesInContext (holesInTail + holesInHead)
