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
SExpPred : Type -> Type
SExpPred atom = !- (SExp atom)

public export
SListPred : Type -> Type
SListPred atom = !- (SList atom)

public export
SPredPair : Type -> Type
SPredPair atom = (SExpPred atom, SListPred atom)

public export
SPredPairList : Type -> Type
SPredPairList atom = List (SPredPair atom)

public export
SExpPi : {atom : Type} -> SExpPred atom -> Type
SExpPi pred = SExp atom ~> pred

public export
SListPi : {atom : Type} -> SListPred atom -> Type
SListPi pred = SList atom ~> pred

public export
SPiPair : {atom : Type} -> SExpPred atom -> SListPred atom -> Type
SPiPair sp lp = (SExpPi sp, SListPi lp)

public export
record SExpEliminatorSig
  {atom : Type} (sp : SExpPred atom) (lp : SListPred atom)
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
    {sp : SExpPred atom} -> {lp : SListPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExpPi sp
  sexpEliminator signature (a $: l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator : {atom : Type} ->
    {sp : SExpPred atom} -> {lp : SListPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SListPi lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x)
      (slistEliminator signature l)

public export
sexpEliminators : {atom : Type} ->
  {sp : SExpPred atom} -> {lp : SListPred atom} ->
  (signature : SExpEliminatorSig sp lp) ->
  SPiPair sp lp
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpEliminatorsComposedPreds :
  {f : Type -> Type} ->
  {atom : Type} ->
  {sp : SExpPred atom} -> {lp : SListPred atom} ->
  (signature : SExpEliminatorSig (f . sp) (f . lp)) ->
  SPiPair (f . sp) (f . lp)
sexpEliminatorsComposedPreds = sexpEliminators

public export
SExpSignatureEliminatorSig :
  {f : Type -> Type} ->
  {da : DependentApplicative f} ->
  {atom : Type} ->
  {sp : SExpPred atom} -> {lp : SListPred atom} ->
  (signature : f (SExpEliminatorSig sp lp)) ->
  SExpEliminatorSig (f . sp) (f . lp)
SExpSignatureEliminatorSig {f} {da} {sp} {lp} signature =
  let mapExpElim = afmap {da} expElim signature in
  let mapNilElim = afmap {da} nilElim signature in
  let mapConsElim = afmap {da} consElim signature in
  SExpEliminatorArgs
    (\a, l, flpl =>
     afapply da (dpure da (dpure da mapExpElim a) l) flpl)
    mapNilElim
    (\x, l, fspx, flpl =>
     afapply da (afapply da (dpure da (dpure da mapConsElim x) l) fspx) flpl)

public export
sexpSignatureEliminators :
  {f : Type -> Type} ->
  {da : DependentApplicative f} ->
  {atom : Type} ->
  {sp : SExpPred atom} -> {lp : SListPred atom} ->
  (signature : f (SExpEliminatorSig sp lp)) ->
  SPiPair (f . sp) (f . lp)
sexpSignatureEliminators {f} {da} {sp} {lp} signature =
  sexpEliminators (SExpSignatureEliminatorSig {f} {da} signature)

public export
sexpTypeConstructors : {atom : Type} ->
  (signature : SExpEliminatorSig {atom} (\_ => Type) (\_ => Type)) ->
  SPredPair atom
sexpTypeConstructors = sexpEliminators

public export
sexpParameterizedEliminators : {atom : Type} ->
  {sp : List (SPredPair atom) -> SExpPred atom} ->
  {lp : List (SPredPair atom) -> SListPred atom} ->
  (parameterizedSignature :
    (params : List (SPredPair atom)) ->
    SExpEliminatorSig (sp params) (lp params)) ->
  (params : List (SPredPair atom)) ->
  SPiPair (sp params) (lp params)
sexpParameterizedEliminators parameterizedSignature params =
  sexpEliminators (parameterizedSignature params)

public export
sexpParameterizedSignatureEliminators :
  {f : Type -> Type} ->
  {da : DependentApplicative f} ->
  {atom : Type} ->
  {sp : List (SPredPair atom) -> SExpPred atom} ->
  {lp : List (SPredPair atom) -> SListPred atom} ->
  (parameterizedSignature :
    (params : List (SPredPair atom)) ->
    f (SExpEliminatorSig (sp params) (lp params))) ->
  (params : List (SPredPair atom)) ->
  SPiPair (f . (sp params)) (f . (lp params))
sexpParameterizedSignatureEliminators {f} {da}
  parameterizedSignature params =
    sexpSignatureEliminators {f} {da} (parameterizedSignature params)

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
  sexpDepFolds {fs} {fl} {sp=(\_ => sp)} {lp=(\_ => lp)} signature context

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
SExpPairEliminatorSigToEliminatorSig : {atom : Type} ->
  {sp : (x, x' : SExp atom) -> Type} -> {lp : (l, l' : SList atom) -> Type} ->
  SExpPairEliminatorSig sp lp ->
  SExpEliminatorSig
    (\x => (x' : SExp atom) -> sp x x')
    (\l => (l' : SList atom) -> lp l l')
SExpPairEliminatorSigToEliminatorSig signature =
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
sexpPairDepFolds : {atom : Type} ->
  {sp : (x, x' : SExp atom) -> Type} -> {lp : (l, l' : SList atom) -> Type} ->
  (signature : SExpPairEliminatorSig sp lp) ->
  ((x, x' : SExp atom) -> sp x x', (l, l' : SList atom) -> lp l l')
sexpPairDepFolds {atom} {sp} {lp} signature =
  sexpEliminators (SExpPairEliminatorSigToEliminatorSig signature)

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
SListForAll : {atom : Type} ->
  (depType : SExp atom -> Type) -> SList atom -> Type
SListForAll = ListForAll . SExpForAll

public export
SExpForAllExp :
  {atom : Type} -> {depType : SExp atom -> Type} ->
  {a : atom} -> {l : SList atom} ->
  SExpForAll depType (a $: l) -> depType (a $: l)
SExpForAllExp (sp :$: _) = sp

public export
SExpForAllList :
  {atom : Type} -> {depType : SExp atom -> Type} ->
  {a : atom} -> {l : SList atom} ->
  SExpForAll depType (a $: l) -> SListForAll depType l
SExpForAllList (_ :$: lp) = lp

public export
SListForAllHead :
  {atom : Type} -> {depType : SExp atom -> Type} ->
  {x : SExp atom} -> {l : SList atom} ->
  SListForAll depType (x $+ l) -> SExpForAll depType x
SListForAllHead (|:|) impossible
SListForAllHead (sp ::: _) = sp

public export
SListForAllTail :
  {atom : Type} -> {depType : SExp atom -> Type} ->
  {x : SExp atom} -> {l : SList atom} ->
  SListForAll depType (x $+ l) -> SListForAll depType l
SListForAllTail (|:|) impossible
SListForAllTail (_ ::: lp) = lp

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
SListExists : {atom : Type} ->
  (depType : SExp atom -> Type) -> SList atom -> Type
SListExists = ListExists . SExpExists

public export
record SExpExistsList
  {atom : Type} (depType : SExp atom -> Type) (x : SExp atom) where
    constructor SExpExistsCons
    SExpExistsHead : SExpExists depType x
    SExpExistsTail : List (SExpExists depType x)

public export
sexpExistsListCons : {atom : Type} -> {depType : SExp atom -> Type} ->
  {x : SExp atom} ->
  SExpExists depType x -> SExpExistsList depType x ->
  SExpExistsList depType x
sexpExistsListCons newHead (SExpExistsCons oldHead tail) =
  SExpExistsCons newHead (oldHead :: tail)

public export
record SListExistsList
  {atom : Type} (depType : SExp atom -> Type) (l : SList atom) where
    constructor SListExistsCons
    SExpExistsHead : SListExists depType l
    SExpExistsTail : List (SListExists depType l)

public export
slistExistsListCons : {atom : Type} -> {depType : SExp atom -> Type} ->
  {l : SList atom} ->
  SListExists depType l -> SListExistsList depType l ->
  SListExistsList depType l
slistExistsListCons newHead (SListExistsCons oldHead tail) =
  SListExistsCons newHead (oldHead :: tail)

public export
slistExistsListAppendList : {atom : Type} -> {depType : SExp atom -> Type} ->
  {l : SList atom} ->
  List (SListExists depType l) ->
  SListExistsList depType l ->
  SListExistsList depType l
slistExistsListAppendList [] exists = exists
slistExistsListAppendList (lx :: llx) exists =
  slistExistsListCons lx (slistExistsListAppendList llx exists)

public export
slistExistsListAppend : {atom : Type} -> {depType : SExp atom -> Type} ->
  {l : SList atom} ->
  SListExistsList depType l -> SListExistsList depType l ->
  SListExistsList depType l
slistExistsListAppend (SListExistsCons leftHead leftTail) right =
  slistExistsListAppendList (leftHead :: leftTail) right

public export
slistExistsExp : {atom : Type} -> {depType : SExp atom -> Type} ->
  {l : SList atom} -> {a : atom} ->
  SListExistsList depType l ->
  SExpExistsList depType (a $: l)
slistExistsExp (SListExistsCons head tail) =
  SExpExistsCons ((>$:) head) (map (>$:) tail)

public export
sexpExistsList : {atom : Type} -> {depType : SExp atom -> Type} ->
  {x : SExp atom} ->
  {l : SList atom} ->
  SExpExistsList depType x ->
  SListExistsList depType (x $+ l)
sexpExistsList (SExpExistsCons head tail) =
  SListExistsCons ((<::) head) (map (<::) tail)

public export
slistExistsShift : {atom : Type} -> {depType : SExp atom -> Type} ->
  {l : SList atom} -> {x : SExp atom} ->
  SListExistsList depType l ->
  SListExistsList depType (x $+ l)
slistExistsShift (SListExistsCons head tail) =
  SListExistsCons ((>::) head) (map (>::) tail)

public export
slistExistsMerge : {atom : Type} -> {depType : SExp atom -> Type} ->
  {x : SExp atom} -> {l : SList atom} ->
  SExpExistsList depType x ->
  SListExistsList depType l ->
  SListExistsList depType (x $+ l)
slistExistsMerge {x} {l} expList listList =
  slistExistsListAppend (sexpExistsList expList) (slistExistsShift listList)

public export
SExpEitherForAll :
  {atom : Type} -> (sl, sr : SExp atom -> Type) -> SExp atom -> Type
SExpEitherForAll sl sr x = Either (SExpForAll sl x) (SExpExistsList sr x)

public export
SListEitherForAll :
  {atom : Type} -> (sl, sr : SExp atom -> Type) -> SList atom -> Type
SListEitherForAll sl sr l = Either (SListForAll sl l) (SListExistsList sr l)

public export
SExpEitherForAllCons : {f : Type -> Type} -> Applicative f =>
  {atom : Type} -> {sl, sr : SExp atom -> Type} ->
  {x : SExp atom} -> {l : SList atom} ->
  f (SExpEitherForAll sl sr x) ->
  f (SListEitherForAll sl sr l) ->
  f (SListEitherForAll sl sr (x $+ l))
SExpEitherForAllCons {f} fs fl =
  map (\eithers => case eithers of
    (Left sForAll, Left lForAll) => Left (sForAll ::: lForAll)
    (Left sForAll, Right lExists) => Right (slistExistsShift lExists)
    (Right sExists, Left lForAll) => Right (sexpExistsList sExists)
    (Right sExists, Right lExists) => Right (slistExistsMerge sExists lExists))
  (applyPair fs fl)

public export
SExpForAllApplications : {f : Type -> Type} -> Applicative f =>
  {atom : Type} -> {depType : SExp atom -> Type} ->
  ((x : SExp atom) -> SExpForAll (f . depType) x -> f (SExpForAll depType x),
   (l : SList atom) -> SListForAll (f . depType) l -> f (SListForAll depType l))
SExpForAllApplications {f} {depType} =
  sexpEliminators
    {sp=(\x => (SExpForAll (f . depType) x) -> f (SExpForAll depType x))}
    {lp=(\l => (SListForAll (f . depType) l) -> f (SListForAll depType l))}
    (SExpEliminatorArgs
      (\a, l, mapLForAll, sForAll =>
        (map (:$:) (SExpForAllExp sForAll)) <*>
        (mapLForAll (SExpForAllList sForAll)))
      (\_ => pure (|:|))
      (\x, l, mapSForAll, mapLForAll, slForAll =>
        (map (:::) (mapSForAll (SListForAllHead slForAll))) <*>
        (mapLForAll (SListForAllTail slForAll))))

public export
SExpForAllApply : {f : Type -> Type} -> Applicative f =>
  {atom : Type} -> {depType : SExp atom -> Type} ->
  (x : SExp atom) -> SExpForAll (f . depType) x -> f (SExpForAll depType x)
SExpForAllApply {f} {depType} = fst (SExpForAllApplications {f} {depType})

public export
SListForAllApply : {f : Type -> Type} -> Applicative f =>
  {atom : Type} -> {depType : SExp atom -> Type} ->
  (l : SList atom) -> SListForAll (f . depType) l -> f (SListForAll depType l)
SListForAllApply {f} {depType} = snd (SExpForAllApplications {f} {depType})

public export
SExpForAllMaps : {f : Type -> Type} ->
  {atom : Type} -> {depType : SExp atom -> Type} ->
  (fmap : (x : SExp atom) -> depType x -> f (depType x)) ->
  ((x : SExp atom) -> SExpForAll depType x -> SExpForAll (f . depType) x,
   (l : SList atom) -> SListForAll depType l -> SListForAll (f . depType) l)
SExpForAllMaps {f} {depType} fmap =
  sexpEliminators
    (SExpEliminatorArgs
      (\a, l, forAllMap, sForAll =>
        fmap (a $: l) (SExpForAllExp sForAll) :$:
          forAllMap (SExpForAllList sForAll))
      (\_ =>
        (|:|))
      (\x, l, sForAllMap, lForAllMap, lForAll =>
        sForAllMap (SListForAllHead lForAll) :::
          lForAllMap (SListForAllTail lForAll)))

public export
record
SExpForAllFoldSig {atom : Type} (sp : SExp atom -> Type) where
  constructor SExpForAllFoldArgs
  expElim :
    (a : atom) -> (l : SList atom) -> SListForAll sp l -> sp (a $: l)

public export
sexpForAllFolds :
  {atom : Type} ->
  {sp : SExp atom -> Type} ->
  (signature : SExpForAllFoldSig sp) ->
  ((x : SExp atom) -> SExpForAll sp x, (l : SList atom) -> SListForAll sp l)
sexpForAllFolds {atom} {sp} signature =
  sexpEliminators
    (SExpEliminatorArgs
      (\a, l, slForAll => expElim signature a l slForAll :$: slForAll)
      (|:|)
      (\x, l, head, tail => head ::: tail))

public export
sexpApplicativeForAllFolds : {f : Type -> Type} ->
  Applicative f =>
  {atom : Type} ->
  {sp : SExp atom -> Type} ->
  (signature : SExpForAllFoldSig (f . sp)) ->
  ((x : SExp atom) -> f (SExpForAll sp x),
   (l : SList atom) -> f (SListForAll sp l))
sexpApplicativeForAllFolds {f} {atom} {sp} signature =
  let forAllFolds = sexpForAllFolds {sp=(f . sp)} signature in
  (\x => SExpForAllApply x (fst forAllFolds x),
   \l => SListForAllApply l (snd forAllFolds l))

public export
record SExpMetaEliminatorSig
  {atom : Type}
  {sp : !- (SExp atom)}
  {lp : !- (SList atom)}
  (signature : SExpEliminatorSig sp lp)
  (spp : (x : SExp atom) -> sp x -> Type)
  (lpp : (l : SList atom) -> lp l -> Type)
  where
    constructor SExpMetaEliminatorArgs
    metaExpElim :
      (a : atom) -> (l : SList atom) ->
      (lppl : lpp l (slistEliminator signature l)) ->
      spp (a $: l) (expElim signature a l (slistEliminator signature l))
    metaNilElim : lpp [] (nilElim signature)
    metaConsElim :
      (x : SExp atom) -> (l : SList atom) ->
      (sppx : spp x (sexpEliminator signature x)) ->
      (lppl : lpp l (slistEliminator signature l)) ->
      lpp (x $+ l)
        (consElim signature x l
          (sexpEliminator signature x)
          (slistEliminator signature l))

public export
sexpMetaEliminators :
  {atom : Type} ->
  {sp : !- (SExp atom)} ->
  {lp : !- (SList atom)} ->
  {signature : SExpEliminatorSig sp lp} ->
  {spp : (x : SExp atom) -> sp x -> Type} ->
  {lpp : (l : SList atom) -> lp l -> Type} ->
  (metaSig : SExpMetaEliminatorSig signature spp lpp) ->
  ((x : SExp atom) -> spp x (sexpEliminator signature x),
   (l : SList atom) -> lpp l (slistEliminator signature l))
sexpMetaEliminators {atom} {sp} {lp} {spp} {lpp} metaSig =
  sexpEliminators
    (SExpEliminatorArgs
      (metaExpElim metaSig) (metaNilElim metaSig) (metaConsElim metaSig))
