module RefinedSExp.SExp

import Category.ComputableCategories
import Decidable.Equality

%default total

mutual
  infixr 7 $:
  public export
  data SExp : Type -> Type where
    ($:) : {atom : Type} -> atom -> SList atom -> SExp atom

  infixr 7 $+
  public export
  data SList : Type -> Type where
    ($|) : {atom : Type} -> SList atom
    ($+) : {atom : Type} -> SExp atom -> SList atom -> SList atom

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

prefix 11 $<*
public export
($<*) : {atom : Type} -> List (SExp atom) -> SList atom
($<*) [] = ($|)
($<*) (x :: l) = x $+ $<* l

prefix 11 $>*
public export
($>*) : {atom : Type} -> SList atom -> List (SExp atom)
($>*) ($|) = []
($>*) (x $+ l) = x :: $>* l

export
ListToSListToListEq : {atom : Type} -> (l : List (SExp atom)) ->
  ($>*) ($<* l) = l
ListToSListToListEq [] = Refl
ListToSListToListEq (x :: l) = cong ((::) x) (ListToSListToListEq l)

export
SListToListToSListEq : {atom : Type} -> (l : SList atom) ->
  ($<*) ($>* l) = l
SListToListToSListEq ($|) = Refl
SListToListToSListEq (x $+ l) = cong (($+) x) (SListToListToSListEq l)

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
SPredicate : (atom : Type) -> Type
SPredicate atom = SExp atom -> Type

public export
SLPredicate : (atom : Type) -> Type
SLPredicate atom = SList atom -> Type

public export
data SLForAll : {atom : Type} -> SPredicate atom -> SLPredicate atom where
  SLForAllEmpty : {atom : Type} -> {predicate : SPredicate atom} ->
    SLForAll predicate ($|)
  SLForAllCons : {atom : Type} -> {predicate : SPredicate atom} ->
    {x : SExp atom} -> {l : SList atom} ->
    predicate x -> SLForAll predicate l -> SLForAll predicate (x $+ l)

mutual
  public export
  sExpInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    (expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)) ->
    (nilElim : lp ($|)) ->
    (consElim :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)) ->
    (x : SExp atom) -> sp x
  sExpInd expElim nilElim consElim (a $: l) =
    expElim a l (sListInd expElim nilElim consElim l)

  public export
  sListInd :
    {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
    (expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)) ->
    (nilElim : lp ($|)) ->
    (consElim :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)) ->
    (l : SList atom) -> lp l
  sListInd expElim nilElim consElim ($|) = nilElim
  sListInd expElim nilElim consElim (x $+ l) =
    consElim x l
      (sExpInd expElim nilElim consElim x) (sListInd expElim nilElim consElim l)

public export
sInd :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  (expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)) ->
  (nilElim : lp ($|)) ->
  (consElim :
      (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)) ->
  ((x : SExp atom) -> sp x, (l : SList atom) -> lp l)
sInd expElim nilElim consElim =
  (sExpInd expElim nilElim consElim, sListInd expElim nilElim consElim)

public export
sIndForAll :
  {atom : Type} -> {sp : SPredicate atom} ->
  (forAllElim :
    (a : atom) -> (l : SList atom) ->
    SLForAll sp l -> sp (a $: l)) ->
  ((x : SExp atom) -> sp x, (l : SList atom) -> SLForAll sp l)
sIndForAll forAllElim = sInd forAllElim SLForAllEmpty (\_, _ => SLForAllCons)
