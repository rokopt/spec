module RefinedSExp.SExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List

%default total

-----------------------
---- S-expressions ----
-----------------------

-- I continue to waffle over representations.  On the whole
-- I think I like this form with an atom and a list because
-- of the separation that it expresses between composition
-- and evaluation, between functional programming and
-- metaprogramming.  I might want to port some of the
-- machinery from the PairVariant, such as the many instances
-- and the well-founded induction (both performing well-founded
-- induction on S-expressions using their size, and using
-- S-expressions to perform well-founded induction on other
-- structures using the S-expressions' shape).

mutual
  infixr 7 $*
  public export
  data SExp : (name : Type) -> Type where
    ($*) : name -> SList name -> SExp name

  public export
  SList : (name : Type) -> Type
  SList = List . SExp

prefix 11 $^
public export
($^) : {name : Type} -> name -> SExp name
($^) n = n $* []

infixr 7 $^:
public export
($^:) : {name : Type} -> name -> SList name -> SList name
n $^: l = $^ n :: l

prefix 11 $*^
public export
($*^) : {name : Type} -> name -> SList name
($*^) n = n $^: []

prefix 11 $**
public export
($**) : {name : Type} -> SExp name -> SList name
($**) x = x :: []

infixr 7 $***
public export
($***) : {name : Type} -> name -> SExp name -> SExp name
n $*** x = n $* $** x

infixr 7 $:*
public export
($:*) : {name : Type} -> SExp name -> SExp name -> SList name
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {name : Type} -> SExp name -> name -> SList name
x $:^ n = x $:* $^ n

infixr 7 $^^
public export
($^^) : {name : Type} -> name -> name -> SList name
n $^^ n' = n $^: $*^ n'

infixr 7 $**^
public export
($**^) : {name : Type} -> name -> name -> SExp name
n $**^ n' = n $* $*^ n'

public export
SPred : (name : Type) -> Type
SPred name = SExp name -> Type

public export
SLPred : (name : Type) -> Type
SLPred name = SList name -> Type

public export
record SExpEliminatorSig
  {name : Type} (0 sp : SPred name) (0 lp : SLPred name)
  where
    constructor SExpEliminatorArgs
    expElim : (n : name) -> (l : SList name) -> lp l -> sp (n $* l)
    nilElim : lp []
    consElim : (x : SExp name) -> (l : SList name) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {name : Type} -> {0 sp : SPred name} -> {0 lp : SLPred name} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp name ~> sp
  sexpEliminator signature (n $* l) =
    expElim signature n l (slistEliminator signature l)

  public export
  slistEliminator :
    {name : Type} -> {0 sp : SPred name} -> {0 lp : SLPred name} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList name ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {name : Type} -> {0 sp : SPred name} -> {0 lp : SLPred name} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp name ~> sp, SList name ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpShows : {name : Type} -> (showName : name -> String) ->
  (SExp name -> String, SList name -> String)
sexpShows {name} showName =
  sexpEliminators $ SExpEliminatorArgs
    (\n, l, lString => case l of
      [] => showName n
      _ :: _ => "(" ++ showName n ++ " $* " ++ lString ++ ")")
    ""
    (\_, l, sx, sl => case l of
      [] => sx
      _ :: _ => sx ++ " : " ++ sl)

mutual
  public export
  sexpDecEq :
    {0 name : Type} -> (nEq : DecEqPred name) -> DecEqPred (SExp name)
  sexpDecEq nEq (n $* l) (n' $* l') =
    case (nEq n n', slistDecEq nEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No nNeq, _) => No $ \eq => case eq of Refl => nNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  slistDecEq :
    {0 name : Type} -> (nEq : DecEqPred name) -> DecEqPred (SList name)
  slistDecEq nEq [] [] = Yes Refl
  slistDecEq nEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  slistDecEq nEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  slistDecEq nEq (x :: l) (x' :: l') =
    case (sexpDecEq nEq x x', slistDecEq nEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

mutual
  public export
  data SExpTransformResult : Type -> Type where
    SExpTransformFailed : SExpTransformResult atom
    SExpUnchanged : SExpTransformResult atom
    SExpChanged : SExp atom -> SExpTransformResult atom

  public export
  data SListTransformResult : Type -> Type where
    SListTransformFailed : SListTransformResult atom
    SListUnchanged : SListTransformResult atom
    SListChanged : SList atom -> SListTransformResult atom

public export
record SExpandSignature (atom : Type) where
  constructor SExpandArgs
  expandOne : SExp atom -> SExpTransformResult atom

mutual
  public export
  sexpExpand : SExpandSignature atom -> SExp atom -> SExpTransformResult atom
  sexpExpand signature (a $* l) = case slistExpand signature l of
    SListTransformFailed => SExpTransformFailed
    SListUnchanged => expandOne signature (a $* l)
    SListChanged l' => SExpChanged (a $* l')

  public export
  slistExpand : SExpandSignature atom -> SList atom -> SListTransformResult atom
  slistExpand _ [] = SListUnchanged
  slistExpand signature (x :: l) = case sexpExpand signature x of
    SExpTransformFailed => SListTransformFailed
    SExpUnchanged => case slistExpand signature l of
      SListTransformFailed => SListTransformFailed
      SListUnchanged => SListUnchanged
      SListChanged l' => SListChanged (x :: l')
    SExpChanged x' => SListChanged (x' :: l)
