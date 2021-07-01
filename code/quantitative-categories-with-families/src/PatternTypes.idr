module PatternTypes

import ComputableCategories
import Decidable.Equality
import public List

%default total


mutual
  infixl 2 $:
  public export
  data SExp : Type -> Type where
    ($:) : {atom : Type} -> atom -> SList atom -> SExp atom

  infixl 3 $+
  public export
  data SList : Type -> Type where
    ($|) : {atom : Type} -> SList atom
    ($+) : {atom : Type} -> SExp atom -> SList atom -> SList atom

public export
SNil : {atom : Type} -> SList atom
SNil = ($|)

public export
SCons : {atom : Type} -> SExp atom -> SList atom -> SList atom
SCons = ($+)

public export
($^) : {atom : Type} -> atom -> SExp atom
($^) a = a $: ($|)

public export
SAtom : {atom : Type} -> atom -> SExp atom
SAtom = ($^)

public export
($<*) : {atom : Type} -> List (SExp atom) -> SList atom
($<*) [] = ($|)
($<*) (x :: l) = x $+ ($<*) l

public export
($>*) : {atom : Type} -> SList atom -> List (SExp atom)
($>*) ($|) = []
($>*) (x $+ l) = x :: ($>*) l

export
ListToSListToListEq : {atom : Type} -> (l : List (SExp atom)) ->
  ($>*) (($<*) l) = l
ListToSListToListEq [] = Refl
ListToSListToListEq (x :: l) = cong ((::) x) (ListToSListToListEq l)

export
SListToListToSListEq : {atom : Type} -> (l : SList atom) ->
  ($<*) (($>*) l) = l
SListToListToSListEq ($|) = Refl
SListToListToSListEq (x $+ l) = cong (($+) x) (SListToListToSListEq l)

public export
($+|) : {atom : Type} -> SExp atom -> SList atom
($+|) x = x $+ ($|)

public export
($^|) : {atom : Type} -> atom -> SList atom
($^|) a = ($+|) (($^) a)

infixl 9 $:|
public export
($:|) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $:| x = a $: ($+|) x

infixl 8 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> SExp atom
a $^^ a' = a $:| ($^) a'

infixl 7 $^+
public export
($^+) : {atom : Type} -> atom -> SList atom -> SList atom
a $^+ l = ($^) a $+ l

infixl 6 $:+
public export
($:+) : {atom : Type} -> atom -> SExp atom -> SList atom
a $:+ x = a $^+ ($+|) x

infixl 6 $:^
public export
($:^) : {atom : Type} -> atom -> atom -> SList atom
a $:^ a' = a $:+ ($^) a'
