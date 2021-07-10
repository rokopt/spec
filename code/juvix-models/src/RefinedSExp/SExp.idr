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
  (atom, sexpContextType, slistContextType,
   sexpPredicate, slistPredicate : Type)
  where
    constructor SExpFoldArgs
    expElim :
      atom -> SList atom ->
        ((context : slistContextType) -> (slistContextType, slistPredicate)) ->
        sexpContextType ->
      (sexpContextType, sexpPredicate)
    nilElim : Void
    consElim : Void

public export
SExpFoldToListSig :
  {atom, sexpContextType, slistContextType,
   sexpPredicate, slistPredicate : Type} ->
  SExpFoldSig
      atom slistContextType sexpContextType sexpPredicate slistPredicate ->
  ListFoldSig
      (SExp atom) sexpContextType slistPredicate_hole
SExpFoldToListSig expSig =
  ListFoldArgs
    (?SExpFoldToListSig_nilElim_hole)
    (?SExpFoldToListSig_consElim_hole)

mutual
  public export
  sexpFoldFlip :
    {atom, sexpContextType, slistContextType,
     sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig
        atom sexpContextType slistContextType sexpPredicate slistPredicate) ->
    (predecessors : SList atom) ->
    (x : SExp atom) ->
    (context : sexpContextType) ->
    (sexpContextType, sexpPredicate)
  sexpFoldFlip signature predecessors (a $: l) =
    expElim signature a l (slistFoldFlip signature ((a $: l) :: predecessors) l)

  public export
  slistFoldFlip :
    {atom, sexpContextType, slistContextType,
     sexpPredicate, slistPredicate : Type} ->
    (signature :
      SExpFoldSig
        atom sexpContextType slistContextType sexpPredicate slistPredicate) ->
    (predecessors : SList atom) ->
    (l : SList atom) ->
    (context : slistContextType) ->
    (slistContextType, slistPredicate)
  slistFoldFlip signature l =
    listFoldFlip {atom=(SExp atom)} (SExpFoldToListSig signature) l

public export
sexpFold :
  {atom, sexpContextType, slistContextType,
   sexpPredicate, slistPredicate : Type} ->
  (signature :
    SExpFoldSig
      atom sexpContextType slistContextType sexpPredicate slistPredicate) ->
  (predecessors : SList atom) ->
  (context : sexpContextType) ->
  (x : SExp atom) ->
  (sexpContextType, sexpPredicate)
sexpFold signature predecessors = flip (sexpFoldFlip signature predecessors)

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
