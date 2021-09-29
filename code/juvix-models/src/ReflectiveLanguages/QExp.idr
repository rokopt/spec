module ReflectiveLanguages.QExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Data.Nat
import public Category.ComputableCategories

%default total

%default total

mutual
  infixr 7 $*
  infixr 7 $>
  public export
  data QExp : (atom : Type) -> (order : Nat) -> Type where
    ($*) : {atom : Type} -> {order : Nat} ->
      atom -> QList atom order -> QExp atom order
    ($>) : {atom : Type} -> {order : Nat} ->
      atom -> QList atom order -> QExp atom (S order)

  public export
  QList : (atom : Type) -> (order : Nat) -> Type
  QList atom order = List $ QExp atom order

prefix 11 $^
public export
($^) : {atom : Type} -> {order : Nat} -> atom -> QExp atom order
($^) a = a $* []

infixr 7 $^:
public export
($^:) : {atom : Type} -> {order : Nat} ->
  atom -> QList atom order -> QList atom order
a $^: l = $^ a :: l

prefix 11 $*^
public export
($*^) : {atom : Type} -> {order : Nat} -> atom -> QList atom order
($*^) a = a $^: []

prefix 11 $**
public export
($**) : {atom : Type} -> {order : Nat} ->
  QExp atom order -> QList atom order
($**) x = x :: []

infixr 7 $***
public export
($***) : {atom : Type} -> {order : Nat} ->
  atom -> QExp atom order -> QExp atom order
a $*** x = a $* $** x

infixr 7 $:*
public export
($:*) : {atom : Type} -> {order : Nat} ->
  QExp atom order -> QExp atom order -> QList atom order
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {atom : Type} -> {order : Nat} ->
  QExp atom order -> atom -> QList atom order
x $:^ a = x $:* $^ a

infixr 7 $^^
public export
($^^) : {atom : Type} -> {order : Nat} -> atom -> atom -> QList atom order
a $^^ a' = a $^: $*^ a'

infixr 7 $**^
public export
($**^) : {atom : Type} -> {order : Nat} -> atom -> atom -> QExp atom order
a $**^ a' = a $* $*^ a'

public export
QPred : (atom : Type) -> Type
QPred atom = (order : Nat) -> QExp atom order -> Type

public export
QLPred : (atom : Type) -> Type
QLPred atom = (order : Nat) -> QList atom order -> Type

public export
record QExpEliminatorSig
  {0 atom : Type} (0 qp : QPred atom) (0 lp : QLPred atom)
  where
    constructor QExpEliminatorArgs
    expElim : (order : Nat) -> (a : atom) -> (l : QList atom order) ->
      lp order l ->
      qp order (a $* l)
    evalElim : (order : Nat) -> (a : atom) -> (l : QList atom order) ->
      ((x : QExp atom order) -> qp order x) ->
      lp order l ->
      qp (S order) (a $> l)
    nilElim : (order : Nat) -> lp order []
    consElim :
      (order : Nat) -> (x : QExp atom order) -> (l : QList atom order) ->
      qp order x -> lp order l -> lp order (x :: l)

mutual
  public export
  qexpEliminator :
    {0 atom : Type} -> {0 qp : QPred atom} -> {0 lp : QLPred atom} ->
    (signature : QExpEliminatorSig qp lp) ->
    (order : Nat) -> (x : QExp atom order) -> qp order x
  qexpEliminator signature order (a $* l) =
    expElim signature order a l
      (qlistEliminator signature order l)
  qexpEliminator signature (S order) (a $> l) =
    evalElim signature order a l
      (qexpEliminator signature order)
      (qlistEliminator signature order l)

  public export
  qlistEliminator :
    {0 atom : Type} -> {0 qp : QPred atom} -> {0 lp : QLPred atom} ->
    (signature : QExpEliminatorSig qp lp) ->
    (order : Nat) -> (l : QList atom order) -> lp order l
  qlistEliminator signature order [] =
    nilElim signature order
  qlistEliminator signature order (x :: l) =
    consElim signature order x l
      (qexpEliminator signature order x) (qlistEliminator signature order l)

public export
qexpEliminators :
  {0 atom : Type} -> {0 qp : QPred atom} -> {0 lp : QLPred atom} ->
  (signature : QExpEliminatorSig qp lp) ->
  ((order : Nat) -> (x : QExp atom order) -> qp order x,
   (order : Nat) -> (l : QList atom order) -> lp order l)
qexpEliminators signature =
  (qexpEliminator signature, qlistEliminator signature)

mutual
  data QExpForAll : {0 atom : Type} ->
      (0 pred : QPred atom) -> QPred atom where
    QExpAndList : {0 pred : QPred atom} -> {order : Nat} ->
      {a : atom} -> {l : QList atom order} ->
      pred order (a $* l) -> QListForAll pred order l ->
      QExpForAll pred order (a $* l)
    QEvalAndList : {0 pred : QPred atom} -> {order : Nat} ->
      {a : atom} -> {l : QList atom order} ->
      pred (S order) (a $> l) -> QListForAll pred order l ->
      QExpForAll pred (S order) (a $> l)

  data QListForAll : {0 atom : Type} ->
      (0 pred : QPred atom) -> QLPred atom where
    QForAllNil : {0 pred : QPred atom} -> {order : Nat} ->
      QListForAll pred order []
    QForAllCons : {0 pred : QPred atom} -> {order : Nat} ->
      {x : QExp atom order} -> {l : QList atom order} ->
      QExpForAll pred order x -> QListForAll pred order l ->
      QListForAll pred order (x :: l)

mutual
  data QExpExists : {0 atom : Type} ->
      (0 pred : QPred atom) -> QPred atom where
    QExpThis : {0 pred : QPred atom} -> {order : Nat} ->
      {x : QExp atom order} ->
      pred order x -> QExpExists pred order x
    QExpInList : {0 pred : QPred atom} -> {order : Nat} ->
      {a : atom} -> {l : QList atom order} ->
      QListExists pred order l -> QExpExists pred order (a $* l)
    QEvalInList : {0 pred : QPred atom} -> {order : Nat} ->
      {a : atom} -> {l : QList atom order} ->
      QListExists pred order l -> QExpExists pred (S order) (a $> l)

  data QListExists : {0 atom : Type} ->
      (0 pred : QPred atom) -> QLPred atom where
    QExpHead : {0 pred : QPred atom} -> {order : Nat} ->
      {x : QExp atom order} -> {l : QList atom order} ->
      QExpExists pred order x -> QListExists pred order (x :: l)
    QExpTail : {0 pred : QPred atom} -> {order : Nat} ->
      {x : QExp atom order} -> {l : QList atom order} ->
      QListExists pred order l -> QListExists pred order (x :: l)

public export
record QExpGeneralInductionSig
  {0 atom : Type} (0 qp : QPred atom)
  where
    constructor QExpGeneralInductionArgs
    expElim : (order : Nat) -> (a : atom) -> (l : QList atom order) ->
      QListForAll qp order l ->
      qp order (a $* l)
    evalElim : (order : Nat) -> (a : atom) -> (l : QList atom order) ->
      ((x : QExp atom order) -> QExpForAll qp order x) ->
      QListForAll qp order l ->
      qp (S order) (a $> l)

public export
QExpGeneralInductionToEliminatorSig : {0 atom : Type} -> {0 qp : QPred atom} ->
  QExpGeneralInductionSig qp ->
  QExpEliminatorSig (QExpForAll qp) (QListForAll qp)
QExpGeneralInductionToEliminatorSig {qp} signature =
  QExpEliminatorArgs
    (\order, a, l, lForAll =>
      QExpAndList (expElim signature order a l lForAll) lForAll)
    (\order, a, l, eval, lForAll =>
      QEvalAndList (evalElim signature order a l eval lForAll) lForAll)
    (\_ => QForAllNil)
    (\_, _, _ => QForAllCons)

public export
qexpGeneralInductions :
  {0 atom : Type} -> {0 qp : QPred atom} ->
  (signature : QExpGeneralInductionSig qp) ->
  ((order : Nat) -> (x : QExp atom order) -> QExpForAll qp order x,
   (order : Nat) -> (l : QList atom order) -> QListForAll qp order l)
qexpGeneralInductions = qexpEliminators . QExpGeneralInductionToEliminatorSig

mutual
  public export
  qexpDecEq :
    {0 atom : Type} -> {order : Nat} ->
    (aEq : DecEqPred atom) -> DecEqPred (QExp atom order)
  qexpDecEq aEq (a $* l) (a' $* l') =
    case (aEq a a', qlistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No aNeq, _) => No $ \eq => case eq of Refl => aNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl
  qexpDecEq aEq (a $* l) (a' $> l') = No $ \eq => case eq of Refl impossible
  qexpDecEq aEq (a $> l) (a' $* l') = No $ \eq => case eq of Refl impossible
  qexpDecEq aEq (a $> l) (a' $> l') =
    case (aEq a a', qlistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No aNeq, _) => No $ \eq => case eq of Refl => aNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  qlistDecEq :
    {0 atom : Type} -> {order : Nat} ->
    (aEq : DecEqPred atom) -> DecEqPred (QList atom order)
  qlistDecEq aEq [] [] = Yes Refl
  qlistDecEq aEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  qlistDecEq aEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  qlistDecEq aEq (x :: l) (x' :: l') =
    case (qexpDecEq aEq x x', qlistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl
