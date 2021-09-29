module ReflectiveLanguages.QExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Data.Nat
import public Category.ComputableCategories

%default total

%default total

mutual
  infixr 7 $*
  public export
  data QExp : (atom : Type) -> Type where
    ($*) : atom -> QList atom -> QExp atom

  public export
  QList : (atom : Type) -> Type
  QList = List . QExp

prefix 11 $^
public export
($^) : {atom : Type} -> atom -> QExp atom
($^) a = a $* []

infixr 7 $^:
public export
($^:) : {atom : Type} -> atom -> QList atom -> QList atom
a $^: l = $^ a :: l

prefix 11 $*^
public export
($*^) : {atom : Type} -> atom -> QList atom
($*^) a = a $^: []

prefix 11 $**
public export
($**) : {atom : Type} -> QExp atom -> QList atom
($**) x = x :: []

infixr 7 $***
public export
($***) : {atom : Type} -> atom -> QExp atom -> QExp atom
a $*** x = a $* $** x

infixr 7 $:*
public export
($:*) : {atom : Type} -> QExp atom -> QExp atom -> QList atom
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {atom : Type} -> QExp atom -> atom -> QList atom
x $:^ a = x $:* $^ a

infixr 7 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> QList atom
a $^^ a' = a $^: $*^ a'

infixr 7 $**^
public export
($**^) : {atom : Type} -> atom -> atom -> QExp atom
a $**^ a' = a $* $*^ a'

public export
QPred : (atom : Type) -> Type
QPred atom = !- (QExp atom)

public export
QLPred : (atom : Type) -> Type
QLPred atom = !- (QList atom)

mutual
  data QExpForAll : {0 atom : Type} -> (0 pred : QPred atom) -> QPred atom where
    QExpAndList : {0 pred : QPred atom} -> pred (a $* l) -> QListForAll pred l ->
      QExpForAll pred (a $* l)

  data QListForAll : {0 atom : Type} -> (0 pred : QPred atom) -> QLPred atom where
    QForAllNil : {0 pred : QPred atom} -> QListForAll pred []
    QForAllCons : {0 pred : QPred atom} ->
      QExpForAll pred x -> QListForAll pred l ->
      QListForAll pred (x :: l)

mutual
  data QExpExists : {0 atom : Type} -> (0 pred : QPred atom) -> QPred atom where
    QExpThis : {0 pred : QPred atom} -> pred x -> QExpExists pred x
    QExpInList : {0 pred : QPred atom} -> QListExists pred l ->
      QExpExists pred (x $* l)

  data QListExists : {0 atom : Type} -> (0 pred : QPred atom) -> QLPred atom where
    QExpHead : {0 pred : QPred atom} -> QExpExists pred x ->
      QListExists pred (x :: l)
    QExpTail : {0 pred : QPred atom} -> QListExists pred l ->
      QListExists pred (x :: l)

public export
record QExpEliminatorSig
  {0 atom : Type} (0 qp : QPred atom) (0 lp : QLPred atom)
  where
    constructor QExpEliminatorArgs
    expElim : (a : atom) -> (l : QList atom) -> lp l -> qp (a $* l)
    nilElim : lp []
    consElim : (x : QExp atom) -> (l : QList atom) ->
      qp x -> lp l -> lp (x :: l)

mutual
  public export
  qexpEliminator :
    {0 atom : Type} -> {0 qp : QPred atom} -> {0 lp : QLPred atom} ->
    (signature : QExpEliminatorSig qp lp) ->
    QExp atom ~> qp
  qexpEliminator signature (a $* l) =
    expElim signature a l (qlistEliminator signature l)

  public export
  qlistEliminator :
    {0 atom : Type} -> {0 qp : QPred atom} -> {0 lp : QLPred atom} ->
    (signature : QExpEliminatorSig qp lp) ->
    QList atom ~> lp
  qlistEliminator signature [] =
    nilElim signature
  qlistEliminator signature (x :: l) =
    consElim signature x l
      (qexpEliminator signature x) (qlistEliminator signature l)

public export
qexpEliminators :
  {0 atom : Type} -> {0 qp : QPred atom} -> {0 lp : QLPred atom} ->
  (signature : QExpEliminatorSig qp lp) ->
  (QExp atom ~> qp, QList atom ~> lp)
qexpEliminators signature =
  (qexpEliminator signature, qlistEliminator signature)

mutual
  public export
  qexpDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (QExp atom)
  qexpDecEq aEq (a $* l) (a' $* l') =
    case (aEq a a', qlistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No aNeq, _) => No $ \eq => case eq of Refl => aNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  qlistDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (QList atom)
  qlistDecEq aEq [] [] = Yes Refl
  qlistDecEq aEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  qlistDecEq aEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  qlistDecEq aEq (x :: l) (x' :: l') =
    case (qexpDecEq aEq x x', qlistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

public export
record QExpGeneralInductionSig
  {0 atom : Type} (0 qp : QPred atom)
  where
    constructor QExpGeneralInductionArgs
    expElim : (a : atom) -> (l : QList atom) -> QListForAll qp l -> qp (a $* l)

public export
QExpGeneralInductionToEliminatorSig : {0 atom : Type} -> {0 qp : QPred atom} ->
  QExpGeneralInductionSig qp ->
  QExpEliminatorSig (QExpForAll qp) (QListForAll qp)
QExpGeneralInductionToEliminatorSig {qp} (QExpGeneralInductionArgs indStep) =
  QExpEliminatorArgs
    (\a, l, lForAll => QExpAndList (indStep a l lForAll) lForAll)
    QForAllNil
    (\_, _ => QForAllCons)

public export
qexpGeneralInductions :
  {0 atom : Type} -> {0 qp : QPred atom} ->
  (signature : QExpGeneralInductionSig qp) ->
  (QExp atom ~> QExpForAll qp, QList atom ~> QListForAll qp)
qexpGeneralInductions = qexpEliminators . QExpGeneralInductionToEliminatorSig
