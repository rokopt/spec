module PatternTypes

import ComputableCategories
import Decidable.Equality
import public List

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

prefix 11 $^|
public export
($^|) : {atom : Type} -> atom -> SList atom
($^|) a = $+| ($^ a)

infixr 7 $:|
public export
($:|) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $:| x = a $: $+| x

infixr 8 $^^
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

{-
infixr 7 $:+
public export
($:+) : {atom : Type} -> atom -> SExp atom -> SList atom
a $:+ x = a $+ $^| x
-}

infixr 8 $:^
public export
($:^) : {atom : Type} -> atom -> atom -> SList atom
a $:^ a' = a $:+ $^ a'
