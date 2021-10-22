module RefinedSExp.SExp

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Data.SortedMap
import public Data.SortedSet
import public Data.Vect

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
  data SExp : (atom : Type) -> Type where
    ($*) : atom -> SList atom -> SExp atom

  public export
  SList : (atom : Type) -> Type
  SList = List . SExp

prefix 11 $^
public export
($^) : {atom : Type} -> atom -> SExp atom
($^) a = a $* []

infixr 7 $^:
public export
($^:) : {atom : Type} -> atom -> SList atom -> SList atom
a $^: l = $^ a :: l

prefix 11 $*^
public export
($*^) : {atom : Type} -> atom -> SList atom
($*^) a = a $^: []

prefix 11 $**
public export
($**) : {atom : Type} -> SExp atom -> SList atom
($**) x = x :: []

infixr 7 $***
public export
($***) : {atom : Type} -> atom -> SExp atom -> SExp atom
a $*** x = a $* $** x

infixr 7 $:*
public export
($:*) : {atom : Type} -> SExp atom -> SExp atom -> SList atom
x $:* x' = x :: $** x'

infixr 7 $:^
public export
($:^) : {atom : Type} -> SExp atom -> atom -> SList atom
x $:^ a = x $:* $^ a

infixr 7 $^^
public export
($^^) : {atom : Type} -> atom -> atom -> SList atom
a $^^ a' = a $^: $*^ a'

infixr 7 $**^
public export
($**^) : {atom : Type} -> atom -> atom -> SExp atom
a $**^ a' = a $* $*^ a'

public export
SPred : (atom : Type) -> Type
SPred atom = SExp atom -> Type

public export
SLPred : (atom : Type) -> Type
SLPred atom = SList atom -> Type

public export
record SExpEliminatorSig
  {atom : Type} (0 sp : SPred atom) (0 lp : SLPred atom)
  where
    constructor SExpEliminatorArgs
    expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $* l)
    nilElim : lp []
    consElim : (x : SExp atom) -> (l : SList atom) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp atom ~> sp
  sexpEliminator signature (a $* l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator :
    {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList atom ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp atom ~> sp, SList atom ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
sexpShows : {atom : Type} -> (showAtom : atom -> String) ->
  (SExp atom -> String, SList atom -> String)
sexpShows {atom} showAtom =
  sexpEliminators $ SExpEliminatorArgs
    (\a, l, lString => case l of
      [] => showAtom a
      _ :: _ => "(" ++ showAtom a ++ " $* " ++ lString ++ ")")
    ""
    (\_, l, sx, sl => case l of
      [] => sx
      _ :: _ => sx ++ " : " ++ sl)

mutual
  public export
  sexpDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (SExp atom)
  sexpDecEq aEq (a $* l) (a' $* l') =
    case (aEq a a', slistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No aNeq, _) => No $ \eq => case eq of Refl => aNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

  public export
  slistDecEq :
    {0 atom : Type} -> (aEq : DecEqPred atom) -> DecEqPred (SList atom)
  slistDecEq aEq [] [] = Yes Refl
  slistDecEq aEq [] (x :: l) = No $ \eq => case eq of Refl impossible
  slistDecEq aEq (x :: l) [] = No $ \eq => case eq of Refl impossible
  slistDecEq aEq (x :: l) (x' :: l') =
    case (sexpDecEq aEq x x', slistDecEq aEq l l') of
      (Yes Refl, Yes Refl) => Yes Refl
      (No xNeq, _) => No $ \eq => case eq of Refl => xNeq Refl
      (_ , No lNeq) => No $ \eq => case eq of Refl => lNeq Refl

mutual
  public export
  sexpLessThan : {0 atom : Type} -> (aLessThan : atom -> atom -> Bool) ->
    SExp atom -> SExp atom -> Bool
  sexpLessThan aLessThan (a $* l) (a' $* l') =
    if (aLessThan a a') then True else slistLessThan aLessThan l l'

  public export
  slistLessThan : {0 atom : Type} -> (aLessThan : atom -> atom -> Bool) ->
    SList atom -> SList atom -> Bool
  slistLessThan _ [] [] = False
  slistLessThan _ [] (_ :: _) = True
  slistLessThan _ (_ :: _) [] = False
  slistLessThan aLessThan (x :: l) (x' :: l') =
    if (sexpLessThan aLessThan x x') then True else slistLessThan aLessThan l l'

mutual
  data SExpForAll : {0 atom : Type} -> SPred atom -> SPred atom where
    SExpAndList : {pred : SPred atom} -> pred (a $* l) -> SListForAll pred l ->
      SExpForAll pred (a $* l)

  data SListForAll : {0 atom : Type} -> SPred atom -> SLPred atom where
    SForAllNil : {pred : SPred atom} -> SListForAll pred []
    SForAllCons : {pred : SPred atom} ->
      SExpForAll pred x -> SListForAll pred l ->
      SListForAll pred (x :: l)

mutual
  data SExpExists : {0 atom : Type} -> SPred atom -> SPred atom where
    SExpThis : {pred : SPred atom} -> pred x -> SExpExists pred x
    SExpInList : {pred : SPred atom} -> SListExists pred l ->
      SExpExists pred (x $* l)

  data SListExists : {0 atom : Type} -> SPred atom -> SLPred atom where
    SExpHead : {pred : SPred atom} -> SExpExists pred x ->
      SListExists pred (x :: l)
    SExpTail : {pred : SPred atom} -> SListExists pred l ->
      SListExists pred (x :: l)

-- | S-expression categories.
mutual
  public export
  ObjectMap : Type -> Type
  ObjectMap atom = SortedMap atom Nat

  public export
  MorphismMap : Type -> Type
  MorphismMap atom = SortedMap atom Void

  public export
  record SCategoryGenerator (scAtom : Type) where
    constructor SCategoryArgs
    identityID : scAtom
    composeID : scAtom
    objectConstructors : ObjectMap scAtom
    morphismConstructors : MorphismMap scAtom

  public export
  data SObject : {scAtom : Type} -> SCategoryGenerator scAtom -> Type where
    SObjConstruct : {scAtom : Type} ->
      (generator : SCategoryGenerator scAtom) ->
      (a : scAtom) -> {auto n : Nat} ->
      {auto isObject : lookup a (objectConstructors generator) = Just n} ->
      Vect n (SObject generator) ->
      SObject generator

mutual
  public export
  sObjInd : {scAtom : Type} -> {generator : SCategoryGenerator scAtom} ->
    {p : SObject generator -> Type} ->
    {pv : (n : Nat) -> Vect n (SObject generator) -> Type} ->
    (objStep : (n : Nat) -> (a : scAtom) ->
      (isObject : lookup a (objectConstructors generator) = Just n) ->
      (objVect : Vect n (SObject generator)) ->
      pv n objVect ->
      p (SObjConstruct generator a objVect)) ->
    (baseCase : pv 0 []) ->
    (indStep : (obj : SObject generator) -> p obj -> (n : Nat) ->
      (objVect : Vect n (SObject generator)) -> pv n objVect ->
      pv (S n) (obj :: objVect)) ->
    (obj : SObject generator) -> p obj
  sObjInd objStep baseCase indStep (SObjConstruct _ a {n} {isObject} objVect) =
    objStep n a isObject objVect
      (sObjVectInd {p} {pv} objStep baseCase indStep objVect)

  public export
  sObjVectInd : {scAtom : Type} -> {generator : SCategoryGenerator scAtom} ->
    {p : SObject generator -> Type} ->
    {pv : (n : Nat) -> Vect n (SObject generator) -> Type} ->
    (objStep : (n : Nat) -> (a : scAtom) ->
      (isObject : lookup a (objectConstructors generator) = Just n) ->
      (objVect : Vect n (SObject generator)) ->
      pv n objVect ->
      p (SObjConstruct generator a objVect)) ->
    (baseCase : pv 0 []) ->
    (indStep : (obj : SObject generator) -> p obj -> (n : Nat) ->
      (objVect : Vect n (SObject generator)) -> pv n objVect ->
      pv (S n) (obj :: objVect)) ->
    {n : Nat} -> (objVect : Vect n (SObject generator)) ->
    pv n objVect
  sObjVectInd objStep baseCase indStep [] = baseCase
  sObjVectInd objStep baseCase indStep {n=(S n')} (obj :: objVect') =
    indStep obj (sObjInd objStep baseCase indStep obj)
      n' objVect' (sObjVectInd objStep baseCase indStep objVect')

public export
(atom : Type) => Show atom => (generator : SCategoryGenerator atom) =>
Show (SObject generator) where
  show = sObjInd
     (\_, a, _, _, vectStr => "<" ++ show a ++ " : " ++ vectStr ++ ">")
     "_"
     (\_, headStr, n, _, tailStr =>
      headStr ++ (if n /= 0 then ", " ++ tailStr else ""))

public export
(atom : Type) => Show atom => (generator : SCategoryGenerator atom) =>
(n : Nat) => Show (Vect n (SObject generator)) where
  show = sObjVectInd
     (\_, a, _, _, vectStr => "<" ++ show a ++ " : " ++ vectStr ++ ">")
     "_"
     (\_, headStr, n, _, tailStr =>
      headStr ++ (if n /= 0 then ", " ++ tailStr else ""))

mutual
  public export
  Show atom => Show (SCategoryGenerator atom) where
    show g = "{Identity : " ++ (show $ identityID g) ++
      ", Compose : " ++ (show $ composeID g) ++
      ", Objects : " ++ (show $ objectConstructors g) ++
      ", Morphisms : " ++ (show $ morphismConstructors g) ++ "}"

mutual
  public export
  sobject : {scAtom : Type} -> (generator : SCategoryGenerator scAtom) ->
    SExp scAtom -> Maybe $ SObject generator
  sobject generator (a $* l) with (lookup a $ objectConstructors generator)
    proof isObject
      sobject generator (a $* l) | Just n = case sobjectVect generator l n of
        Just svect => Just $ SObjConstruct generator a {isObject} svect
        Nothing => Nothing
      sobject generator (a $* l) | Nothing = Nothing

  public export
  sobjectVect : {scAtom : Type} -> (generator : SCategoryGenerator scAtom) ->
    SList scAtom -> (expectedLength : Nat) ->
    Maybe $ Vect expectedLength $ SObject generator
  sobjectVect generator [] 0 = Just []
  sobjectVect generator [] (S _) = Nothing
  sobjectVect generator (_ :: _) 0 = Nothing
  sobjectVect generator (x :: l) (S n) =
    case (sobject generator x, sobjectVect generator l n) of
      (Just x', Just l') => Just (x' :: l')
      _ => Nothing
