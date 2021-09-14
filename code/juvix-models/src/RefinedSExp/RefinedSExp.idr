module RefinedSExp.RefinedSExp

import public Library.Decidability
import public Data.Nat
import public Data.HVect

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
    SSubst : {holesInContext, holesInPattern, holesInArguments : Nat} ->
      StructExp holesInContext holesInPattern ->
      Vect holesInPattern (StructExp holesInContext holesInArguments) ->
      StructExp holesInContext holesInArguments

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

public export
StructPred : Type
StructPred =
  (holesInContext, holesInExpression : Nat) ->
  StructExp holesInContext holesInExpression ->
  Type

public export
StructListPred : Type
StructListPred =
  (holesInContext, holesInExpression : Nat) ->
  StructList holesInContext holesInExpression ->
  Type

-- | The signature of the (mutual) induction principle for structural
-- | expressions and lists.
public export
record StructInductionSig (xp : StructPred) (lp : StructListPred) where
  constructor StructInductionArgs
  referenceElim : (holesInContext : Nat) -> (index : Fin holesInContext) ->
    xp holesInContext 0 ($< index)
  newHoleElim : (holesInContext : Nat) ->
    xp holesInContext 1 ($>)
  listElim : (holesInContext, holesInList : Nat) ->
    (l : StructList holesInContext holesInList) ->
    lp holesInContext holesInList l ->
    xp holesInContext holesInList ($| l)
  substElim : (holesInContext, holesInPattern, holesInArguments : Nat) ->
    (x : StructExp holesInContext holesInPattern) ->
    (args : Vect holesInPattern (StructExp holesInContext holesInArguments)) ->
    xp holesInContext holesInPattern x ->
    HVect (map (xp holesInContext holesInArguments) args) ->
    xp holesInContext holesInArguments (SSubst x args)
  nilElim : (holesInContext : Nat) ->
    lp holesInContext 0 ($-)
  consElim : (holesInContext, holesInHead, holesInTail : Nat) ->
    (x : StructExp holesInContext holesInHead) ->
    (l : StructList (holesInHead + holesInContext) holesInTail) ->
    xp holesInContext holesInHead x ->
    lp (holesInHead + holesInContext) holesInTail l ->
    lp holesInContext (holesInTail + holesInHead) (x $: l)

-- | The signature of the (mutual) induction principle for structural
-- | expressions and lists.
mutual
  structInduction : {xp : StructPred} -> {lp : StructListPred} ->
    StructInductionSig xp lp ->
    (holesInContext, holesInExpression : Nat) ->
    (x : StructExp holesInContext holesInExpression) ->
    xp holesInContext holesInExpression x
  structInduction signature holesInContext 0 ($< fin) =
    referenceElim signature holesInContext fin
  structInduction signature holesInContext 1 ($>) =
    newHoleElim signature holesInContext
  structInduction signature holesInContext holesInExpression ($| l) =
    listElim signature holesInContext holesInExpression l
      (structListInduction signature holesInContext holesInExpression l)
  structInduction signature holesInContext holesInExpression
    (SSubst {holesInContext} {holesInPattern}
      {holesInArguments=holesInExpression} x args) =
        substElim signature holesInContext holesInPattern holesInExpression
          x args
          (structInduction signature
            holesInContext holesInPattern x)
          (structVectInduction signature
            holesInContext holesInPattern holesInExpression args)

  structListInduction : {xp : StructPred} -> {lp : StructListPred} ->
    StructInductionSig xp lp ->
    (holesInContext, holesInList : Nat) ->
    (l : StructList holesInContext holesInList) ->
    lp holesInContext holesInList l
  structListInduction signature holesInContext 0 ($-) =
    nilElim signature holesInContext
  structListInduction signature holesInContext (holesInTail + holesInHead)
    (h $: t) =
      consElim signature holesInContext holesInHead holesInTail h t
        (structInduction signature holesInContext holesInHead h)
        (structListInduction
          signature (holesInHead + holesInContext) holesInTail t)

  structVectInduction : {xp : StructPred} -> {lp : StructListPred} ->
    StructInductionSig xp lp ->
    (holesInContext, numArguments, holesInArguments : Nat) ->
    (args : Vect numArguments (StructExp holesInContext holesInArguments)) ->
    HVect (map (xp holesInContext holesInArguments) args)
  structVectInduction signature
    holesInContext 0 holesInArguments [] =
      []
  structVectInduction signature
    holesInContext (S predNumArguments) holesInArguments (arg :: args) =
      structInduction signature
        holesInContext holesInArguments arg ::
      structVectInduction signature
        holesInContext predNumArguments holesInArguments args

structInductions : {xp : StructPred} -> {lp : StructListPred} ->
  StructInductionSig xp lp ->
  ((holesInContext, holesInExpression : Nat) ->
    (x : StructExp holesInContext holesInExpression) ->
    xp holesInContext holesInExpression x,
   (holesInContext, holesInList : Nat) ->
    (l : StructList holesInContext holesInList) ->
    lp holesInContext holesInList l)
structInductions signature =
  (structInduction signature, structListInduction signature)

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
