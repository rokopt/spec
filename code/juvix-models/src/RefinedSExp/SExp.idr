module RefinedSExp.SExp

import Library.FunctionsAndRelations
import Library.Decidability
import public RefinedSExp.List
import public Category.Category

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
record SExpEliminatorSig
  {atom : Type} (sp : SExp atom -> Type) (lp : SList atom -> Type)
  where
    constructor SExpEliminatorArgs
    expElim :
      (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)
    nilElim :
      lp []
    consElim :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)

mutual
  public export
  sexpEliminator : {atom : Type} ->
  {sp : SExp atom -> Type} ->
  {lp : SList atom -> Type} ->
  (signature : SExpEliminatorSig sp lp) ->
  (x : SExp atom) -> sp x
  sexpEliminator signature (a $: l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator : {atom : Type} ->
  {sp : SExp atom -> Type} ->
  {lp : SList atom -> Type} ->
  (signature : SExpEliminatorSig sp lp) ->
  (l : SList atom) -> lp l
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x)
      (slistEliminator signature l)

public export
sexpEliminators : {atom : Type} ->
  {sp : !- (SExp atom)} ->
  {lp : !- (SList atom)} ->
  (signature : SExpEliminatorSig sp lp) ->
  ((x : SExp atom) -> sp x, (l : SList atom) -> lp l)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpTypeConstructors : {atom : Type} ->
  (signature : SExpEliminatorSig {atom} (\_ => Type) (\_ => Type)) ->
  (!- (SExp atom), !- (SList atom))
sexpTypeConstructors = sexpEliminators

public export
sexpParameterizedEliminators : {atom : Type} ->
  {sp : (!- (SExp atom)) -> (!- (SList atom)) -> (!- (SExp atom))} ->
  {lp : (!- (SExp atom)) -> (!- (SList atom)) -> (!- (SList atom))} ->
  (parameterizedSignature :
    (spParam : (!- (SExp atom))) ->
    (lpParam : (!- (SList atom))) ->
    SExpEliminatorSig (sp spParam lpParam) (lp spParam lpParam)) ->
  (spParam : (!- (SExp atom))) -> (lpParam : (!- (SList atom))) ->
  (SExp atom ~> sp spParam lpParam, SList atom ~> lp spParam lpParam)
sexpParameterizedEliminators parameterizedSignature spParam lpParam =
  sexpEliminators
    (SExpEliminatorArgs
      (expElim (parameterizedSignature spParam lpParam))
      (nilElim (parameterizedSignature spParam lpParam))
      (consElim (parameterizedSignature spParam lpParam)))

public export
SExpEliminatorListPred : {atom : Type} ->
  (sp : SExp atom -> Type) -> (lp : SList atom -> Type) ->
  SList atom -> Type
SExpEliminatorListPred sp lp [] = lp []
SExpEliminatorListPred sp lp (x :: l) = sp x -> lp (x :: l)

export
sexpEliminatorListPredToListPred : {atom : Type} ->
  {sp : SExp atom -> Type} -> {lp : SList atom -> Type} ->
  (signature : SExpEliminatorSig sp lp) ->
  (l : SList atom) -> SExpEliminatorListPred sp lp l -> lp l
sexpEliminatorListPredToListPred signature [] pred =
  pred
sexpEliminatorListPredToListPred signature (x :: l) pred =
  pred (sexpEliminator signature x)

export
SExpEliminatorSigToListSig : {atom : Type} ->
  {sp : SExp atom -> Type} -> {lp : SList atom -> Type} ->
  (signature : SExpEliminatorSig sp lp) ->
  ListEliminatorSig {lp=(SExpEliminatorListPred sp lp)}
SExpEliminatorSigToListSig signature =
  ListEliminatorArgs
    (nilElim signature)
    (\x, l, pred, spx =>
      consElim signature x l spx
        (sexpEliminatorListPredToListPred signature l pred))

export
slistEliminatorMatchesListFold : {atom : Type} ->
  {sp : SExp atom -> Type} ->
  {lp : SList atom -> Type} ->
  (signature : SExpEliminatorSig sp lp) ->
  (l : SList atom) ->
  slistEliminator {sp} {lp} signature l =
    sexpEliminatorListPredToListPred signature l
      (listEliminator (SExpEliminatorSigToListSig signature) l)
slistEliminatorMatchesListFold signature [] =
  Refl
slistEliminatorMatchesListFold signature (x :: l) =
  applyEq {f=(consElim signature x l (sexpEliminator signature x))} Refl
    (slistEliminatorMatchesListFold signature l)

public export
SExpContextPred : (atom : Type) -> (contextType : Type) -> Type
SExpContextPred atom contextType =
  (context : contextType) -> SExp atom -> Type

public export
SListContextPred : (atom : Type) -> (contextType : Type) -> Type
SListContextPred atom contextType =
  (context : contextType) -> SList atom -> Type

public export
SExpDepFoldSig :
  (fs, fl : Type -> Type) -> {atom : Type} -> {contextType : Type} ->
  (sp : SExpContextPred atom contextType) ->
  (lp : SListContextPred atom contextType) ->
  Type
SExpDepFoldSig fs fl {atom} {contextType} sp lp =
  SExpEliminatorSig {atom}
    (\x => (context : contextType) -> fs (contextType, sp context x))
    (\l => (context : contextType) -> fl (contextType, lp context l))

public export
sexpDepFoldFlip :
  {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpContextPred atom contextType} ->
  {lp : SListContextPred atom contextType} ->
  (signature : SExpDepFoldSig fs fl sp lp) ->
  (x : SExp atom) ->
  (context : contextType) ->
  fs (contextType, sp context x)
sexpDepFoldFlip = sexpEliminator

public export
sexpDepFold :
  {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpContextPred atom contextType} ->
  {lp : SListContextPred atom contextType} ->
  (signature : SExpDepFoldSig fs fl sp lp) ->
  (context : contextType) ->
  (x : SExp atom) -> fs (contextType, sp context x)
sexpDepFold {fs} {fl} {sp} signature context x =
  sexpDepFoldFlip {fs} {fl} {sp} signature x context

public export
slistDepFoldFlip :
  {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpContextPred atom contextType} ->
  {lp : SListContextPred atom contextType} ->
  (signature : SExpDepFoldSig fs fl sp lp) ->
  (l : SList atom) ->
  (context : contextType) ->
  fl (contextType, lp context l)
slistDepFoldFlip = slistEliminator

public export
slistDepFold :
  {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpContextPred atom contextType} ->
  {lp : SListContextPred atom contextType} ->
  (signature : SExpDepFoldSig fs fl sp lp) ->
  (context : contextType) ->
  (l : SList atom) -> fl (contextType, lp context l)
slistDepFold {fs} {fl} {lp} signature context l =
  slistDepFoldFlip {fs} {fl} {lp} signature l context

public export
sexpDepFolds :
  {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpContextPred atom contextType} ->
  {lp : SListContextPred atom contextType} ->
  (signature : SExpDepFoldSig fs fl sp lp) ->
  (context : contextType) ->
  ((x : SExp atom) -> fs (contextType, sp context x),
   (l : SList atom) -> fl (contextType, lp context l))
sexpDepFolds {fs} {fl} {sp} {lp} signature context =
  (sexpDepFold {fs} {fl} {sp} {lp} signature context,
   slistDepFold {fs} {fl} {sp} {lp} signature context)

public export
sexpDepFoldsContextIndependent :
  {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExp atom -> Type} ->
  {lp : SList atom -> Type} ->
  (signature : SExpDepFoldSig {contextType} fs fl (\_ => sp) (\_ => lp)) ->
  (context : contextType) ->
  ((x : SExp atom) -> fs (contextType, sp x),
   (l : SList atom) -> fl (contextType, lp l))
sexpDepFoldsContextIndependent {fs} {fl} {sp} {lp} signature context =
  (sexpDepFold {fs} {fl} {sp=(\_ => sp)} {lp=(\_ => lp)} signature context,
   slistDepFold {fs} {fl} {sp=(\_ => sp)} {lp=(\_ => lp)} signature context)

public export
record SExpPairEliminatorSig
  {atom : Type}
  (sp : (x, x' : SExp atom) -> Type) (lp : (l, l' : SList atom) -> Type)
  where
    constructor SExpPairEliminatorArgs
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
sexpPairDepFolds : {atom : Type} ->
  {sp : (x, x' : SExp atom) -> Type} -> {lp : (l, l' : SList atom) -> Type} ->
  (signature : SExpPairEliminatorSig sp lp) ->
  ((x, x' : SExp atom) -> sp x x', (l, l' : SList atom) -> lp l l')
sexpPairDepFolds {atom} {sp} {lp} signature =
  sexpEliminators
    {sp=(\x => (x' : SExp atom) -> sp x x')}
    {lp=(\l => (l' : SList atom) -> lp l l')}
    (SExpEliminatorArgs expCase nilCase consCase)
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
  sexpPairDepFolds
    (SExpPairEliminatorArgs
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
record SExpNonDepListFoldSig
  {atom : Type} (sp : Type)
  where
    constructor SExpNonDepListFoldArgs
    expElim :
      (a : atom) -> (l : SList atom) ->
      (recursiveResult : List sp) ->
      sp

SExpNonDepListFoldSigToEliminatorSig :
  {atom : Type} -> {sp : Type} ->
  SExpNonDepListFoldSig {atom} sp ->
  SExpEliminatorSig
    {atom} (\_ => sp) (\_ => List sp)
SExpNonDepListFoldSigToEliminatorSig signature =
  SExpEliminatorArgs (expElim signature) [] (\_, _ => (::))

public export
sexpNonDepListFolds : {atom : Type} ->
  {sp : Type} ->
  (signature : SExpNonDepListFoldSig {atom} sp) ->
  ((x : SExp atom) -> sp, (l : SList atom) -> List sp)
sexpNonDepListFolds signature =
  sexpEliminators (SExpNonDepListFoldSigToEliminatorSig signature)

infixr 7 :$:
public export
data SExpForAll :
  {atom : Type} -> (depType : SExp atom -> Type) -> SExp atom -> Type where
    (:$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            depType (a $: l) ->
            ListForAll (SExpForAll depType) l ->
            SExpForAll depType (a $: l)

public export
data SExpExists :
  {atom : Type} -> (depType : SExp atom -> Type) -> SExp atom -> Type where
    (<$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            depType (a $: l) ->
            SExpExists depType (a $: l)
    (>$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            ListExists (SExpExists depType) l ->
            SExpExists depType (a $: l)

public export
record SExpExistsList
  {atom : Type} (depType : SExp atom -> Type) (x : SExp atom) where
    constructor SExpExistsCons
    SExpExistsHead : SExpExists depType x
    SExpExistsTail : List (SExpExists depType x)

public export
SListForAll : {atom : Type} ->
  (depType : SExp atom -> Type) -> SList atom -> Type
SListForAll = ListForAll . SExpForAll

public export
SListExists : {atom : Type} ->
  (depType : SExp atom -> Type) -> SList atom -> Type
SListExists = ListExists . SExpExists

public export
record
SExpForAllFoldSig {f : Type -> Type} {atom : Type}
  (sp : SExp atom -> Type) where
    constructor SExpForAllFoldArgs
    expElim :
      (a : atom) -> (l : SList atom) ->
      f (SListForAll sp l) -> f (sp (a $: l))

public export
sexpForAllFolds : {f : Type -> Type} ->
  Applicative f =>
  {atom : Type} ->
  {sp : SExp atom -> Type} ->
  (signature : SExpForAllFoldSig {f} sp) ->
  ((x : SExp atom) -> f (SExpForAll sp x),
   (l : SList atom) -> f (SListForAll sp l))
sexpForAllFolds {f} {atom} {sp} signature =
  sexpEliminators
    {sp=(f . SExpForAll sp)} {lp=(f . SListForAll sp)}
    (SExpEliminatorArgs
      (\a, l, slForAll =>
        map (:$:) (expElim {f} signature a l slForAll) <*> slForAll)
      (pure (|:|))
      (\x, l, head, tail => (map (:::) head) <*> tail))

SExpMetaPred : (f : Type -> Type) ->
  (metaContextType : Type) -> {atom : Type} -> {contextType : Type} ->
  SExpContextPred atom contextType ->
  Type
SExpMetaPred f metaContextType {atom} {contextType} sp =
  metaContextType ->
  (context : contextType) ->
  (x : SExp atom) ->
  f (contextType, sp context x) -> Type

SListMetaPred : (f : Type -> Type) ->
  (metaContextType : Type) -> {atom : Type} -> {contextType : Type} ->
  SListContextPred atom contextType ->
  Type
SListMetaPred f metaContextType {atom} {contextType} lp =
  metaContextType ->
  (context : contextType) ->
  (l : SList atom) ->
  f (contextType, lp context l) -> Type

public export
record SExpMetaFoldSig {fs, fl : Type -> Type}
  {atom : Type} {contextType : Type}
  {sp : SExpContextPred atom contextType}
  {lp : SListContextPred atom contextType}
  (signature : SExpDepFoldSig fs fl sp lp)
  {metaContextType : Type}
  (sdp : SExpMetaPred fs metaContextType sp)
  (ldp : SListMetaPred fl metaContextType lp)
  where
    constructor SExpMetaFoldArgs
    metaExpElim :
      (a : atom) -> (l : SList atom) ->
      (recursiveCall :
        (calledMetaContext : metaContextType) ->
        (metaContextType,
         (calledContext : contextType) ->
           ldp calledMetaContext calledContext l
           (slistDepFold {fs} {fl} {sp} {lp} signature calledContext l))) ->
      (metaContextUponEntry : metaContextType) ->
      (metaContextType,
       (contextUponEntry : contextType) ->
        sdp metaContextUponEntry contextUponEntry (a $: l)
          (expElim signature a l
            (slistDepFoldFlip {fs} {fl} {sp} {lp} signature l)
            contextUponEntry))
    metaNilElim :
      (metaContext : metaContextType) ->
      (metaContextType,
       (context : contextType) ->
       ldp metaContext context [] (nilElim signature context))
    metaConsElim :
      (x : SExp atom) -> (l : SList atom) ->
      (headCall :
        (calledMetaContext: metaContextType) ->
          (metaContextType,
           (calledContext : contextType) ->
           sdp calledMetaContext calledContext x
            (sexpDepFoldFlip {fs} {fl} {sp} {lp}
              signature x calledContext))) ->
      (tailCall :
        (calledMetaContext : metaContextType) ->
         (metaContextType,
          (calledContext : contextType) ->
          ldp calledMetaContext calledContext l
            (slistDepFoldFlip {fs} {fl} {sp} {lp}
              signature l calledContext))) ->
      (metaContextUponEntry : metaContextType) ->
      (metaContextType,
       (contextUponEntry : contextType) ->
        ldp metaContextUponEntry contextUponEntry (x :: l)
        (consElim signature x l
          (sexpDepFoldFlip {fs} {fl} {sp} {lp} signature x)
          (slistDepFoldFlip {fs} {fl} {sp} {lp} signature l)
          contextUponEntry))

public export
sexpMetaFolds : {fs, fl : Type -> Type} ->
  {atom : Type} -> {contextType : Type} ->
  {sp : SExpContextPred atom contextType} ->
  {lp : SListContextPred atom contextType} ->
  {signature : SExpDepFoldSig fs fl sp lp} ->
  {metaContextType : Type} ->
  {sdp : SExpMetaPred fs metaContextType sp} ->
  {ldp : SListMetaPred fl metaContextType lp} ->
  (metaSig : SExpMetaFoldSig {fs} {fl} {sp} {lp} signature sdp ldp) ->
  (metaContext : metaContextType) ->
  ((x : SExp atom) ->
    (metaContextType, (context : contextType) ->
     sdp metaContext context x
      (sexpDepFold {fs} {fl} {sp} {lp} signature context x)),
   (l : SList atom) ->
    (metaContextType, (context : contextType) ->
      ldp metaContext context l
        (slistDepFold {fs} {fl} {sp} {lp} signature context l)))
sexpMetaFolds {fs} {fl} {sp} {lp} {metaContextType} {sdp} {ldp} metaSig =
  sexpDepFolds {contextType=metaContextType}
    {fs=(Prelude.Basics.id)} {fl=(Prelude.Basics.id)}
    (SExpEliminatorArgs
      (metaExpElim metaSig)
      (metaNilElim metaSig)
      (metaConsElim metaSig))

public export
record SExpMetaEliminatorSig
  {f : Type -> Type}
  {atom : Type}
  {sp : !- (SExp atom)}
  {lp : !- (SList atom)}
  (signature : SExpEliminatorSig (f . sp) (f . lp))
  (spp : (x : SExp atom) -> f (sp x) -> Type)
  (lpp : (l : SList atom) -> f (lp l) -> Type)
  where
    constructor SExpMetaEliminatorArgs
    metaExpElim :
      (a : atom) -> (l : SList atom) ->
      (lppl : f (lpp l (slistEliminator signature l))) ->
      f (spp (a $: l) (expElim signature a l (slistEliminator signature l)))
    metaNilElim : f (lpp [] (nilElim signature))
    metaConsElim :
      (x : SExp atom) -> (l : SList atom) ->
      (sppx : f (spp x (sexpEliminator signature x))) ->
      (lppl : f (lpp l (slistEliminator signature l))) ->
      f (lpp (x $+ l)
          (consElim signature x l
            (sexpEliminator signature x)
            (slistEliminator signature l)))

public export
sexpMetaEliminators :
  {f : Type -> Type} ->
  {atom : Type} ->
  {sp : !- (SExp atom)} ->
  {lp : !- (SList atom)} ->
  {signature : SExpEliminatorSig (f . sp) (f . lp)} ->
  {spp : (x : SExp atom) -> f (sp x) -> Type} ->
  {lpp : (l : SList atom) -> f (lp l) -> Type} ->
  (metaSig : SExpMetaEliminatorSig {f} signature spp lpp) ->
  ((x : SExp atom) -> f (spp x (sexpEliminator signature x)),
   (l : SList atom) -> f (lpp l (slistEliminator signature l)))
sexpMetaEliminators {f} {atom} {sp} {lp} {spp} {lpp} metaSig =
  sexpEliminators
    (SExpEliminatorArgs
      (metaExpElim metaSig) (metaNilElim metaSig) (metaConsElim metaSig))
