module RefinedSExp.SExp

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
      -- XXX get rid of predecessors from non-dep one after dep one is done
      (predecessors : SList atom) ->
      atom -> SList atom ->
      (contextType -> (contextType, slistPredicate)) ->
      contextType ->
      (contextType, sexpPredicate)
    nilElim :
      -- XXX get rid of predecessors from non-dep one after dep one is done
      (predecessors : SList atom) ->
      contextType ->
      (contextType, slistPredicate)
    consElim :
      -- XXX get rid of predecessors from non-dep one after dep one is done
      (predecessors : SList atom) ->
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
    (predecessors : SList atom) ->
    (x : SExp atom) ->
    (context : contextType) ->
    (contextType, sexpPredicate)
  sexpFoldFlip signature predecessors (a $: l) =
    expElim signature predecessors a l
      (slistFoldFlip signature ((a $: l) :: predecessors) l)

  public export
  slistFoldFlip :
    {atom, contextType, sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig
        atom contextType sexpPredicate slistPredicate) ->
    (predecessors : SList atom) ->
    (l : SList atom) ->
    (context : contextType) ->
    (contextType, slistPredicate)
  slistFoldFlip signature predecessors l =
    listFoldFlip {atom=(SExp atom)} (SExpFoldToListSig signature) predecessors l

public export
sexpFold : {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature : SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  (predecessors : SList atom) ->
  (context : contextType) ->
  (x : SExp atom) ->
  (contextType, sexpPredicate)
sexpFold signature predecessors = flip (sexpFoldFlip signature predecessors)

public export
slistFold :
  {atom, contextType, sexpPredicate, slistPredicate : Type} ->
  (signature : SExpFoldSig atom contextType sexpPredicate slistPredicate) ->
  (predecessors : SList atom) ->
  (context : contextType) ->
  (l : SList atom) ->
  (contextType, slistPredicate)
slistFold signature predecessors = flip (slistFoldFlip signature predecessors)

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
