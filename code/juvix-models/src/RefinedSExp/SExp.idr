module RefinedSExp.SExp

import Library.FunctionsAndRelations
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
($+) x l = x :: l

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
  (atom, contextType, sexpPredicate, slistPredicate : Type)
  where
    constructor SExpFoldArgs
    expElim :
      atom -> SList atom ->
      (contextType -> (contextType, slistPredicate)) ->
      contextType ->
      (contextType, sexpPredicate)
    nilElim :
      contextType ->
      (contextType, slistPredicate)
    consElim :
      SExp atom -> SList atom ->
      (contextType -> (contextType, slistPredicate)) ->
      contextType ->
      (contextType, slistPredicate)

public export
SExpFoldToListSig :
  {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  SExpFoldSig
      atom contextType sexpPredicate slistPredicate ->
  ListFoldSig
      (SExp atom) contextType slistPredicate
SExpFoldToListSig expSig = ListFoldArgs (nilElim expSig) (consElim expSig)

mutual
  public export
  sexpFoldFlip :
    {atom, contextType, sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig
        atom contextType sexpPredicate slistPredicate) ->
    (x : SExp atom) ->
    (context : contextType) ->
    (contextType, sexpPredicate)
  sexpFoldFlip signature (a $: l) =
    expElim signature a l (slistFoldFlip signature l)

  public export
  slistFoldFlip :
    {atom, contextType, sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig
        atom contextType sexpPredicate slistPredicate) ->
    (l : SList atom) ->
    (context : contextType) ->
    (contextType, slistPredicate)
  slistFoldFlip signature l =
    listFoldFlip {atom=(SExp atom)} (SExpFoldToListSig signature) l

public export
sexpFold : {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature : SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  (context : contextType) ->
  (x : SExp atom) ->
  (contextType, sexpPredicate)
sexpFold signature = flip (sexpFoldFlip signature)

public export
slistFold :
  {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature : SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  (context : contextType) ->
  (l : SList atom) ->
  (contextType, slistPredicate)
slistFold signature = flip (slistFoldFlip signature)

infixr 7 :$:
public export
data SExpForAll :
  {atom : Type} -> (depType : SExp atom -> type) -> SExp atom -> Type where
    (:$:) : {atom : Type} -> {depType : SExp atom -> Type} ->
            {a : atom} -> {l : SList atom} ->
            depType (a $: l) -> ListForAll depType l ->
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
            ListExists depType l ->
            SExpExists depType (a $: l)

SExpPredicate : {atom : Type} -> (contextType : SList atom -> Type) -> Type
SExpPredicate {atom} contextType =
  (predecessors : SList atom) -> (context : contextType predecessors) ->
  SExp atom -> Type

SListPredicate : {atom : Type} -> (contextType : SList atom -> Type) -> Type
SListPredicate {atom} contextType =
  (predecessors : SList atom) -> (context : contextType predecessors) ->
  SList atom -> Type

public export
record SExpDepFoldSig
  {atom : Type} {contextType : SList atom -> Type}
  (sp : SExpPredicate contextType) (lp : SListPredicate contextType)
  where
    constructor SExpDepFoldArgs
    expElim :
      (predecessors : SList atom) ->
      (a : atom) -> (l : SList atom) ->
      (recursiveCall :
        (calledContext : contextType ((a $: l) :: predecessors)) ->
         (contextType ((a $: l) :: predecessors),
          lp ((a $: l) :: predecessors) calledContext l)) ->
      (context : contextType predecessors) ->
      (contextType predecessors, sp predecessors context (a $: l))
    nilElim :
      (predecessors : SList atom) -> (context : contextType predecessors) ->
      (contextType predecessors, lp predecessors context [])
    consElim :
      (predecessors : SList atom) ->
      (x : SExp atom) -> (l : SList atom) ->
      (recursiveCall :
        (calledContext : contextType (x :: predecessors)) ->
        (contextType (x :: predecessors),
         lp (x :: predecessors) calledContext l)) ->
      (contextUponEntry : contextType predecessors) ->
      (contextType predecessors,
       lp predecessors contextUponEntry (x :: l))

public export
SExpDepFoldToListSig :
  {atom : Type} -> {contextType : SList atom -> Type} ->
  {sp : SExpPredicate contextType} -> {lp : SListPredicate contextType} ->
  SExpDepFoldSig sp lp ->
  ListDepFoldSig {atom=(SExp atom)} {contextType} lp
SExpDepFoldToListSig expSig = ListDepFoldArgs (nilElim expSig) (consElim expSig)

mutual
  public export
  sexpDepFoldFlip :
    {atom : Type} -> {contextType : SList atom -> Type} ->
    {sp : SExpPredicate contextType} -> {lp : SListPredicate contextType} ->
    (signature : SExpDepFoldSig sp lp) ->
    {predecessors : SList atom} ->
    (x : SExp atom) ->
    (context : contextType predecessors) ->
    (contextType predecessors, sp predecessors context x)
  sexpDepFoldFlip signature {predecessors} (a $: l) =
    SExpDepFoldSig.expElim signature predecessors a l
      (slistDepFoldFlip signature {predecessors=((a $: l) :: predecessors)} l)

  public export
  slistDepFoldFlip :
    {atom : Type} -> {contextType : SList atom -> Type} ->
    {sp : SExpPredicate contextType} -> {lp : SListPredicate contextType} ->
    (signature : SExpDepFoldSig sp lp) ->
    {predecessors : SList atom} ->
    (l : SList atom) ->
    (context : contextType predecessors) ->
    (contextType predecessors, lp predecessors context l)
  slistDepFoldFlip signature predecessors l =
    listDepFoldFlip (SExpDepFoldToListSig signature) predecessors l

public export
sexpDepFold :
  {atom : Type} -> {contextType : SList atom -> Type} ->
  {sp : SExpPredicate contextType} -> {lp : SListPredicate contextType} ->
  (signature : SExpDepFoldSig sp lp) ->
  {predecessors : SList atom} ->
  (context : contextType predecessors) ->
  (x : SExp atom) -> (contextType predecessors, sp predecessors context x)
sexpDepFold signature context x = sexpDepFoldFlip signature x context

public export
slistDepFold :
  {atom : Type} -> {contextType : SList atom -> Type} ->
  {sp : SExpPredicate contextType} -> {lp : SListPredicate contextType} ->
  (signature : SExpDepFoldSig sp lp) ->
  {predecessors : SList atom} ->
  (context : contextType predecessors) ->
  (l : SList atom) -> (contextType predecessors, lp predecessors context l)
slistDepFold signature context l = slistDepFoldFlip signature l context

public export
sexpDepFolds :
  {atom : Type} -> {contextType : SList atom -> Type} ->
  {sp : SExpPredicate contextType} -> {lp : SListPredicate contextType} ->
  (signature : SExpDepFoldSig sp lp) ->
  ({predecessors : SList atom} ->
    (context : contextType predecessors) ->
    (x : SExp atom) -> (contextType predecessors, sp predecessors context x),
   {predecessors : SList atom} ->
    (context : contextType predecessors) ->
    (l : SList atom) -> (contextType predecessors, lp predecessors context l))
sexpDepFolds signature = (sexpDepFold signature, slistDepFold signature)

public export
SExpFoldNonDepSigToDepSig :
  {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature : SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  SExpDepFoldSig 
    {atom} {contextType=(\_ => contextType)}
    (\_, _, _ => sexpPredicate) (\_, _, _ => slistPredicate)
SExpFoldNonDepSigToDepSig signature =
  SExpDepFoldArgs
    (\_ => expElim signature)
    (\_ => nilElim signature)
    (\_ => consElim signature)

mutual
  export
  sexpDepFoldFlipCorrect :
    {atom, contextType, sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
    {predecessors : SList atom} ->
    (x : SExp atom) ->
    (context : contextType) ->
    sexpFoldFlip signature x context =
      sexpDepFoldFlip
        {atom} {contextType=(\_ => contextType)}
        {sp=(\_, _, _ => sexpPredicate)} {lp=(\_, _, _ => slistPredicate)}
        (SExpFoldNonDepSigToDepSig signature)
        {predecessors}
        x
        context
  sexpDepFoldFlipCorrect signature (a $: l) context =
    ?sexpDepFoldFlipCorrect_hole

  export
  slistDepFoldFlipCorrect :
    {atom, contextType, sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
    {predecessors : SList atom} ->
    (l : SList atom) ->
    (context : contextType) ->
    slistFoldFlip signature l context =
      slistDepFoldFlip
        {atom} {contextType=(\_ => contextType)}
        {sp=(\_, _, _ => sexpPredicate)} {lp=(\_, _, _ => slistPredicate)}
        (SExpFoldNonDepSigToDepSig signature)
        {predecessors}
        l
        context
  slistDepFoldFlipCorrect signature [] context = Refl
  slistDepFoldFlipCorrect signature {predecessors} (x :: l) context =
    let foo = listDepFoldFlipCorrect (SExpFoldToListSig signature) l in
    let bar = applyEq foo {x=context} in
    -- cong (consElim (SExpFoldNonDepSigToDepSig signature) predecessors x l) ?slistDepFoldFlipCorrect_hole_2
    replace
      {p=
        (\v =>
          SExpDepFoldSig.consElim (SExpFoldNonDepSigToDepSig signature)
            predecessors x l v context =
          SExpFoldSig.consElim signature x l v context)}
      foo
      ?argh

export
sexpDepFoldCorrect :
  {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature :
    SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  {predecessors : SList atom} ->
  (context : contextType) ->
  (x : SExp atom) ->
  sexpFold signature context x =
    sexpDepFold
      {atom} {contextType=(\_ => contextType)}
      {sp=(\_, _, _ => sexpPredicate)} {lp=(\_, _, _ => slistPredicate)}
      (SExpFoldNonDepSigToDepSig signature)
      {predecessors}
      context
      x
sexpDepFoldCorrect signature context (a $: l) =
  sexpDepFoldFlipCorrect signature (a $: l) context

export
slistDepFoldCorrect :
  {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature :
    SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  {predecessors : SList atom} ->
  (context : contextType) ->
  (l : SList atom) ->
  slistFold signature context l =
    slistDepFold
      {atom} {contextType=(\_ => contextType)}
      {sp=(\_, _, _ => sexpPredicate)} {lp=(\_, _, _ => slistPredicate)}
      (SExpFoldNonDepSigToDepSig signature)
      {predecessors}
      context
      l
slistDepFoldCorrect signature context l =
  slistDepFoldFlipCorrect signature l context
