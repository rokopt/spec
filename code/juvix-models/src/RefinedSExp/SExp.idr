module RefinedSExp.SExp

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.List

%default total

infixr 7 $:
public export
data SExp : Type -> Type where
  ($:) : {atom : Type} -> atom -> List (SExp atom) -> SExp atom

public export
SList : Type -> Type
SList = List . SExp

public export
($|) : {atom : Type} -> SList atom
($|) = []

infixr 7 $+
public export
($+) : {atom : Type} -> SExp atom -> SList atom -> SList atom
($+) = (::)

public export
SCons : {atom : Type} -> atom -> SList atom -> SExp atom
SCons = ($:)

public export
SNil : {atom : Type} -> SList atom
SNil = ($|)

public export
SLCons : {atom : Type} -> SExp atom -> SList atom -> SList atom
SLCons = ($+)

prefix 11 $^
public export
($^) : {atom : Type} -> atom -> SExp atom
($^) a = a $: ($|)

public export
SAtom : {atom : Type} -> atom -> SExp atom
SAtom = ($^)

prefix 11 <$
public export
(<$) : {atom : Type} -> SExp atom -> atom
(<$) (a $: _) = a

prefix 11 >$
public export
(>$) : {atom : Type} -> SExp atom -> SList atom
(>$) (_ $: l) = l

prefix 11 $+|
public export
($+|) : {atom : Type} -> SExp atom -> SList atom
($+|) x = x $+ ($|)

infixr 7 $++
public export
($++) : {atom : Type} -> SExp atom -> SExp atom -> SList atom
x $++ x' = x $+ $+| x'

infixr 7 $+^
public export
($+^) : {atom : Type} -> SExp atom -> atom -> SList atom
x $+^ a = x $++ $^ a

prefix 11 $^|
public export
($^|) : {atom : Type} -> atom -> SList atom
($^|) a = $+| ($^ a)

infixr 7 $:|
public export
($:|) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $:| x = a $: $+| x

infixr 7 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> SExp atom
a $^^ a' = a $:| $^ a'

infixr 7 $^+
public export
($^+) : {atom : Type} -> atom -> SList atom -> SList atom
a $^+ l = $^ a $+ l

infixr 7 $:+
public export
($:+) : {atom : Type} -> atom -> SExp atom -> SList atom
a $:+ x = a $^+ $+| x

infixr 7 $:^
public export
($:^) : {atom : Type} -> atom -> atom -> SList atom
a $:^ a' = a $:+ $^ a'

public export
record SExpFoldSig
  (atom, contextType, sp, lp : Type)
  where
    constructor SExpFoldArgs
    expElim :
      atom -> SList atom ->
      (contextType -> (contextType, lp)) ->
      contextType -> (contextType, sp)
    snilElim :
      (context : contextType) -> (contextType, lp)
    sconsElim :
      (x : SExp atom) -> (l : SList atom) ->
      (headCall : contextType -> (contextType, sp)) ->
      (tailCall : contextType -> (contextType, lp)) ->
      contextType -> (contextType, lp)

mutual
  public export
  sexpFoldFlip :
    {atom, contextType, sp, lp : Type} ->
    (signature :
      SExpFoldSig
        atom contextType sp lp) ->
    (x : SExp atom) ->
    (context : contextType) ->
    (contextType, sp)
  sexpFoldFlip signature (a $: l) =
    expElim signature a l (slistFoldFlip signature l)

  public export
  slistFoldFlip :
    {atom, contextType, sp, lp : Type} ->
    (signature :
      SExpFoldSig
        atom contextType sp lp) ->
    (l : SList atom) ->
    (context : contextType) ->
    (contextType, lp)
  slistFoldFlip signature [] = snilElim signature
  slistFoldFlip signature (x :: l) =
    sconsElim
      signature x l (sexpFoldFlip signature x) (slistFoldFlip signature l)

public export
sexpFold : {atom, contextType, sp, lp : Type} ->
  (signature : SExpFoldSig atom contextType sp lp) ->
  (context : contextType) ->
  (x : SExp atom) ->
  (contextType, sp)
sexpFold signature = flip (sexpFoldFlip signature)

public export
slistFold :
  {atom, contextType, sp, lp : Type} ->
  (signature : SExpFoldSig atom contextType sp lp) ->
  (context : contextType) ->
  (l : SList atom) -> (contextType, lp)
slistFold signature = flip (slistFoldFlip signature)

public export
sexpFolds : {atom, contextType, sp, lp : Type} ->
  (signature : SExpFoldSig atom contextType sp lp) ->
  (context : contextType) ->
  ((x : SExp atom) -> (contextType, sp),
   (l : SList atom) -> (contextType, lp))
sexpFolds signature context =
  (sexpFold signature context, slistFold signature context)

SExpPredicate : (atom : Type) -> (contextType : Type) -> Type
SExpPredicate atom contextType =
  (context : contextType) -> SExp atom -> Type

SListPredicate : (atom : Type) -> (contextType : Type) -> Type
SListPredicate atom contextType =
  (context : contextType) -> SList atom -> Type

public export
record SExpDepFoldSig
  {atom : Type} {contextType : Type}
  (sp : SExpPredicate atom contextType) (lp : SListPredicate atom contextType)
  where
    constructor SExpDepFoldArgs
    sdepExpElim :
      (a : atom) -> (l : SList atom) ->
      (recursiveCall :
        (calledContext : contextType) ->
         (contextType,
          lp calledContext l)) ->
      (context : contextType) ->
      (contextType, sp context (a $: l))
    sdepNilElim :
      (context : contextType) ->
      (contextType, lp context [])
    sdepConsElim :
      (x : SExp atom) -> (l : SList atom) ->
      (headCall :
        (calledContext : contextType) ->
        (contextType,
         sp calledContext x)) ->
      (tailCall :
        (calledContext : contextType) ->
        (contextType,
         lp calledContext l)) ->
      (contextUponEntry : contextType) ->
      (contextType, lp contextUponEntry (x :: l))

mutual
  public export
  sexpDepFoldFlip :
    {atom : Type} -> {contextType : Type} ->
    {sp : SExpPredicate atom contextType} ->
    {lp : SListPredicate atom contextType} ->
    (signature : SExpDepFoldSig sp lp) ->
    (x : SExp atom) ->
    (context : contextType) ->
    (contextType, sp context x)
  sexpDepFoldFlip {atom} signature (a $: l) =
    sdepExpElim {atom} signature a l
      (slistDepFoldFlip signature l)

  public export
  slistDepFoldFlip :
    {atom : Type} -> {contextType : Type} ->
    {sp : SExpPredicate atom contextType} ->
    {lp : SListPredicate atom contextType} ->
    (signature : SExpDepFoldSig sp lp) ->
    (l : SList atom) ->
    (context : contextType) ->
    (contextType, lp context l)
  slistDepFoldFlip signature [] =
    (sdepNilElim signature)
  slistDepFoldFlip signature (x :: l) =
    sdepConsElim signature x l
      (sexpDepFoldFlip signature x)
      (slistDepFoldFlip signature l)

public export
sexpDepFold :
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpPredicate atom contextType} ->
  {lp : SListPredicate atom contextType} ->
  (signature : SExpDepFoldSig sp lp) ->
  (context : contextType) ->
  (x : SExp atom) -> (contextType, sp context x)
sexpDepFold signature context x = sexpDepFoldFlip signature x context

public export
slistDepFold :
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpPredicate atom contextType} ->
  {lp : SListPredicate atom contextType} ->
  (signature : SExpDepFoldSig sp lp) ->
  (context : contextType) ->
  (l : SList atom) -> (contextType, lp context l)
slistDepFold signature context l = slistDepFoldFlip signature l context

public export
sexpDepFolds :
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpPredicate atom contextType} ->
  {lp : SListPredicate atom contextType} ->
  (signature : SExpDepFoldSig sp lp) ->
  (context : contextType) ->
  ((x : SExp atom) -> (contextType, sp context x),
   (l : SList atom) -> (contextType, lp context l))
sexpDepFolds signature context =
  (sexpDepFold signature context, slistDepFold signature context)

public export
SExpFoldNonDepSigToDepSig :
  {atom, contextType, sp, lp : Type} ->
  (signature : SExpFoldSig atom contextType sp lp) ->
  SExpDepFoldSig 
    {atom} {contextType}
    (\_, _ => sp) (\_, _ => lp)
SExpFoldNonDepSigToDepSig signature =
  SExpDepFoldArgs
    (expElim signature)
    (snilElim signature)
    (sconsElim signature)

mutual
  export
  sexpDepFoldFlipCorrect :
    {atom, contextType, sp, lp : Type} ->
    (signature :
      SExpFoldSig atom contextType sp lp) ->
    (x : SExp atom) ->
    sexpFoldFlip signature x =
      sexpDepFoldFlip
        {atom} {contextType}
        {sp=(\_, _ => sp)} {lp=(\_,_ => lp)}
        (SExpFoldNonDepSigToDepSig signature)
        x
  sexpDepFoldFlipCorrect signature (a $: l) =
    cong (expElim signature a l) (slistDepFoldFlipCorrect signature l)

  export
  slistDepFoldFlipCorrect :
    {atom, contextType, sp, lp : Type} ->
    (signature :
      SExpFoldSig atom contextType sp lp) ->
    (l : SList atom) ->
    slistFoldFlip signature l =
      slistDepFoldFlip
        {atom} {contextType}
        {sp=(\_, _ => sp)} {lp=(\_, _ => lp)}
        (SExpFoldNonDepSigToDepSig signature)
        l
  slistDepFoldFlipCorrect signature [] = Refl
  slistDepFoldFlipCorrect signature (x :: l) =
    let
      headEq = sexpDepFoldFlipCorrect signature x
      tailEq = slistDepFoldFlipCorrect signature l
      congHead = cong (sconsElim signature x l) headEq
    in
    applyEq congHead tailEq

export
sexpDepFoldCorrect :
  {atom, contextType, sp, lp : Type} ->
  (signature :
    SExpFoldSig atom contextType sp lp) ->
  (context : contextType) ->
  (x : SExp atom) ->
  sexpFold signature context x =
    sexpDepFold
      {atom} {contextType}
      {sp=(\_, _ => sp)} {lp=(\_, _ => lp)}
      (SExpFoldNonDepSigToDepSig signature)
      context
      x
sexpDepFoldCorrect signature context (a $: l) =
  applyEq (sexpDepFoldFlipCorrect signature (a $: l)) Refl

export
slistDepFoldCorrect :
  {atom, contextType, sp, lp : Type} ->
  (signature :
    SExpFoldSig atom contextType sp lp) ->
  (context : contextType) ->
  (l : SList atom) ->
  slistFold signature context l =
    slistDepFold
      {atom} {contextType}
      {sp=(\_, _ => sp)} {lp=(\_, _ => lp)}
      (SExpFoldNonDepSigToDepSig signature)
      context
      l
slistDepFoldCorrect signature context l =
  applyEq (slistDepFoldFlipCorrect signature l) Refl

public export
record SExpDepContextFreeFoldSig
  {atom : Type} (sp : SExp atom -> Type) (lp : SList atom -> Type)
  where
    constructor SExpDepContextFreeFoldArgs
    expElim :
      (a : atom) -> (l : SList atom) ->
      (recursiveResult : lp l) ->
      sp (a $: l)
    nilElim : lp []
    consElim :
      (x : SExp atom) -> (l : SList atom) ->
      (headResult : sp x) ->
      (tailResult : lp l) ->
      lp (x $+ l)

public export
SExpDepContextFreeFoldSigToDepFoldSig :
  {atom : Type} -> {sp : SExp atom -> Type} -> {lp : SList atom -> Type} ->
  SExpDepContextFreeFoldSig {atom} sp lp ->
  SExpDepFoldSig
    {atom} {contextType=()} (\_ => sp) (\_ => lp)
SExpDepContextFreeFoldSigToDepFoldSig signature =
  SExpDepFoldArgs
    (\a, l, tailCall, _ => ((), expElim signature a l (snd (tailCall ()))))
    (\_ => ((), nilElim signature))
    (\x, l, headCall, tailCall, _ =>
      ((), consElim signature x l (snd (headCall ())) (snd (tailCall ()))))

public export
sexpDepContextFreeFolds : {atom : Type} ->
  {sp : SExp atom -> Type} ->
  {lp : SList atom -> Type} ->
  (signature : SExpDepContextFreeFoldSig sp lp) ->
  ((x : SExp atom) -> sp x, (l : SList atom) -> lp l)
sexpDepContextFreeFolds signature =
  let
    folds =
      sexpDepFolds (SExpDepContextFreeFoldSigToDepFoldSig signature) ()
  in
  (\x => snd (fst folds x), \l => snd (snd folds l))

public export
record SExpDepContextFreePairFoldSig
  {atom : Type}
  (sp : (x, x' : SExp atom) -> Type) (lp : (l, l' : SList atom) -> Type)
  where
    constructor SExpDepContextFreePairFoldArgs
    expElim :
      (a : atom) -> (l : SList atom) -> (a' : atom) -> (l' : SList atom) ->
      (lpl : lp l l') -> sp (a $: l) (a' $: l')
    nilNilElim : lp [] []
    nilConsElim : (x' : SExp atom) -> (l' : SList atom) -> lp [] (x' :: l')
    consNilElim : (x : SExp atom) -> (l : SList atom) -> lp (x :: l) []
    consConsElim :
      (x: SExp atom) -> (l : SList atom) ->
      (x' : SExp atom) -> (l' : SList atom) ->
      (spx : sp x x') -> (lpl : lp l l') ->
      lp (x $+ l) (x' $+ l')

public export
sexpDepContextFreePairFolds : {atom : Type} ->
  {sp : (x, x' : SExp atom) -> Type} -> {lp : (l, l' : SList atom) -> Type} ->
  (signature : SExpDepContextFreePairFoldSig sp lp) ->
  ((x, x' : SExp atom) -> sp x x', (l, l' : SList atom) -> lp l l')
sexpDepContextFreePairFolds {atom} {sp} {lp} signature =
  sexpDepContextFreeFolds
    {sp=(\x => (x' : SExp atom) -> sp x x')}
    {lp=(\l => (l' : SList atom) -> lp l l')}
    (SExpDepContextFreeFoldArgs expCase nilCase consCase)
    where
      expCase : (a : atom) -> (l : SList atom) ->
        (lpf : (l' : SList atom) -> lp l l') -> (x : SExp atom) ->
        sp (a $: l) x
      expCase a l lpf (a' $: l') = expElim signature a l a' l' (lpf l')

      nilCase : (l' : SList atom) -> lp [] l'
      nilCase [] = nilNilElim signature
      nilCase (x' :: l') = nilConsElim signature x' l'

      consCase : (x : SExp atom) -> (l : SList atom) ->
        (spf : (x' : SExp atom) -> sp x  x') ->
        (lpf : (l' : SList atom) -> lp l l') ->
        (l' : SList atom) -> lp (x :: l)  l'
      consCase x l spf lpf [] =
        consNilElim signature x l
      consCase x l spf lpf (x' :: l') =
        consConsElim signature x l x' l' (spf x') (lpf l')

public export
sexpDecEq : {atom : Type} ->
  (atomDecEq : DecEqPred atom) ->
  ((x, x' : SExp atom) -> Dec (x = x'), (l, l' : SList atom) -> Dec (l = l'))
sexpDecEq atomDecEq =
  sexpDepContextFreePairFolds
    (SExpDepContextFreePairFoldArgs
      (\a, l, a', l', leq => case (atomDecEq a a', leq) of
        (Yes Refl, Yes Refl) => Yes Refl
        (No aneq, _) => No (\eq => case eq of Refl => aneq Refl)
        (_, No lneq) => No (\eq => case eq of Refl => lneq Refl))
      (Yes Refl)
      (\_, _ => No (\eq => case eq of Refl impossible))
      (\_, _ => No (\eq => case eq of Refl impossible))
      (\x, l, x', l', xeq, leq => case (xeq, leq) of
        (Yes Refl, Yes Refl) => Yes Refl
        (No xneq, _) => No (\eq => case eq of Refl => xneq Refl)
        (_, No lneq) => No (\eq => case eq of Refl => lneq Refl)))

public export
record SExpNonDepContextFreeFoldListSig
  {atom : Type} (sp : Type)
  where
    constructor SExpNonDepContextFreeFoldListArgs
    expElim :
      (a : atom) -> (l : SList atom) ->
      (recursiveResult : List sp) ->
      sp

public export
SExpNonDepContextFreeFoldListSigToContextFreeFoldSig :
  {atom : Type} -> {sp : Type} ->
  SExpNonDepContextFreeFoldListSig {atom} sp ->
  SExpDepContextFreeFoldSig
    {atom} (\_ => sp) (\_ => List sp)
SExpNonDepContextFreeFoldListSigToContextFreeFoldSig signature =
  SExpDepContextFreeFoldArgs (expElim signature) [] (\_, _ => (::))

public export
sexpNonDepContextFreeListFolds : {atom : Type} ->
  {sp : Type} ->
  (signature : SExpNonDepContextFreeFoldListSig {atom} sp) ->
  ((x : SExp atom) -> sp, (l : SList atom) -> List sp)
sexpNonDepContextFreeListFolds {atom} signature =
  sexpDepContextFreeFolds {atom} {sp=(\_ => sp)} {lp=(\_ => List sp)}
    (SExpNonDepContextFreeFoldListSigToContextFreeFoldSig signature)

infixr 7 :$:
public export
data SExpForAll :
  {atom : Type} -> (depType : SExp atom -> type) -> SExp atom -> Type where
    (:$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            depType (a $: l) ->
            ListForAll (SExpForAll depType) l ->
            SExpForAll depType (a $: l)

public export
data SExpExists :
  {atom : Type} -> (depType : SExp atom -> type) -> SExp atom -> Type where
    (<$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            depType (a $: l) ->
            SExpExists depType (a $: l)
    (>$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            ListExists (SExpExists depType) l ->
            SExpExists depType (a $: l)

public export
SListForAll : {atom : Type} ->
  (depType : SExp atom -> type) -> SList atom -> Type
SListForAll = ListForAll . SExpForAll

public export
SListExists : {atom : Type} ->
  (depType : SExp atom -> type) -> SList atom -> Type
SListExists = ListExists . SExpExists

public export
record
SExpForAllFoldSig {atom : Type}
  (sp : SExp atom -> Type) where
    constructor SExpForAllFoldArgs
    expElim :
      (a : atom) -> (l : SList atom) -> SListForAll sp l -> sp (a $: l)

public export
sexpForAllFolds : {atom : Type} ->
  {sp : SExp atom -> Type} ->
  (signature : SExpForAllFoldSig sp) ->
  ((x : SExp atom) -> SExpForAll sp x, (l : SList atom) -> SListForAll sp l)
sexpForAllFolds signature =
  sexpDepContextFreeFolds
    {sp=(SExpForAll sp)} {lp=(SListForAll sp)}
    (SExpDepContextFreeFoldArgs
      (\a, l, slForAll => expElim signature a l slForAll :$: slForAll)
      (|:|)
      (\_, _, head, tail => head ::: tail))

-- A fold which uses a context, but which produces a predicate
-- independent of the context (i.e. dependent only on the s-expression itself).
public export
record SExpDepFoldContextIndependentSig
  {atom : Type}
  (contextType : Type)
  (sp : SExp atom -> Type)
  (lp : SList atom -> Type)
  where
    constructor SExpDepFoldContextIndependentArgs
    expElim :
      (a : atom) -> (l : SList atom) ->
      (contextType -> (contextType, lp l)) ->
      (contextType -> (contextType, sp (a $: l)))
    nilElim : contextType -> (contextType, lp [])
    consElim :
      (x : SExp atom) -> (l : SList atom) ->
      (headCall : contextType -> (contextType, sp x)) ->
      (tailCall : contextType -> (contextType, lp l)) ->
      (contextType -> (contextType, lp (x :: l)))

public export
sexpDepFoldsContextIndependent : {atom : Type} ->
  {contextType : Type} ->
  {sp : SExp atom -> Type} ->
  {lp : SList atom -> Type} ->
  (signature : SExpDepFoldContextIndependentSig contextType sp lp) ->
  contextType ->
  ((x : SExp atom) -> (contextType, sp x),
   (l : SList atom) -> (contextType, lp l))
sexpDepFoldsContextIndependent {contextType} {sp} signature =
  sexpDepFolds
    (SExpDepFoldArgs
      (expElim signature)
      (nilElim signature)
      (consElim signature))

-- A for-all fold which uses a context, but which produces a predicate
-- independent of the context (i.e. dependent only on the s-expression itself).
public export
record SExpForAllFoldContextIndependentSig
  {atom : Type}
  (contextType : Type)
  (sp : SExp atom -> Type)
  where
    constructor SExpForAllFoldContextIndependentArgs
    expElim :
      (a : atom) -> (l : SList atom) ->
      (contextType, SListForAll sp l) ->
      (contextType, sp (a $: l))

public export
sexpForAllFoldsContextIndependent : {atom : Type} ->
  {contextType : Type} ->
  {sp : SExp atom -> Type} ->
  (signature : SExpForAllFoldContextIndependentSig contextType sp) ->
  contextType ->
  ((x : SExp atom) -> (contextType, SExpForAll sp x),
   (l : SList atom) -> (contextType, SListForAll sp l))
sexpForAllFoldsContextIndependent {contextType} {sp} signature =
  sexpDepFoldsContextIndependent
    {contextType}
    {sp=(SExpForAll sp)}
    {lp=(SListForAll sp)}
    (SExpDepFoldContextIndependentArgs
      (\a, l, tailCall, context =>
        let slForAll = tailCall context in
        let sp = expElim signature a l slForAll in
        (fst sp, snd sp :$: snd slForAll))
      (\context => (context, (|:|)))
      (\x, l, headCall, tailCall, context =>
        let head = headCall context in
        let tail = tailCall (fst head) in
        (fst tail, snd head ::: snd tail)))

SExpMetaPred :
  {atom : Type} -> {contextType : Type} ->
  SExpPredicate atom contextType ->
  Type
SExpMetaPred {atom} {contextType} sp =
  (context : contextType) ->
  (x : SExp atom) ->
  (contextType, sp context x) -> Type

SListMetaPred :
  {atom : Type} -> {contextType : Type} ->
  SListPredicate atom contextType ->
  Type
SListMetaPred {atom} {contextType} lp =
  (context : contextType) ->
  (l : SList atom) ->
  (contextType, lp context l) -> Type

public export
record SExpMetaFoldSig
  {atom : Type} {contextType : Type}
  {sp : SExpPredicate atom contextType} {lp : SListPredicate atom contextType}
  (signature : SExpDepFoldSig sp lp)
  (sdp : SExpMetaPred sp)
  (ldp : SListMetaPred lp)
  where
    constructor SExpMetaFoldArgs
    metaExpElim :
      (a : atom) -> (l : SList atom) ->
      (recursiveCall :
        (calledContext : contextType) ->
        ldp calledContext l
          (slistDepFoldFlip signature l calledContext)) ->
      (contextUponEntry : contextType) ->
      sdp contextUponEntry (a $: l)
        (sdepExpElim signature a l
          (slistDepFoldFlip signature l) contextUponEntry)
    metaNilElim :
      (context : contextType) ->
      ldp context [] (sdepNilElim signature context)
    metaConsElim :
      (x : SExp atom) -> (l : SList atom) ->
      (headCall :
          (calledContext : contextType) ->
          sdp calledContext x
            (sexpDepFoldFlip signature x calledContext)) ->
      (tailCall :
          (calledContext : contextType) ->
          ldp calledContext l
            (slistDepFoldFlip signature l calledContext)) ->
      (contextUponEntry : contextType) ->
      ldp contextUponEntry (x :: l)
        (sdepConsElim signature x l
          (sexpDepFoldFlip signature x)
          (slistDepFoldFlip signature l)
          contextUponEntry)

public export
sexpMetaFolds :
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpPredicate atom contextType} ->
  {lp : SListPredicate atom contextType} ->
  {signature : SExpDepFoldSig sp lp} ->
  {sdp : SExpMetaPred sp} ->
  {ldp : SListMetaPred lp} ->
  (metaSig : SExpMetaFoldSig signature sdp ldp) ->
  ((context : contextType) ->
    (x : SExp atom) ->
    sdp context x (sexpDepFold signature context x),
   (context : contextType) ->
    (l : SList atom) ->
    ldp context l (slistDepFold signature context l))
sexpMetaFolds {signature} {sdp} {ldp} metaSig =
  let
    folds =
      sexpDepContextFreeFolds
        (SExpDepContextFreeFoldArgs
          (metaExpElim metaSig)
          (metaNilElim metaSig)
          (metaConsElim metaSig))
  in
  (\context, x => fst folds x context,
   \context, l => snd folds l context)
