module Decidability

import FunctionsAndRelations
import public Data.Vect
import public Decidable.Equality
import public Data.Maybe

%default total

public export
IsTrue : Bool -> Type
IsTrue b = (b = True)

public export
isYes : {t: Type} -> Dec t -> Bool
isYes (Yes _) = True
isYes (No _) = False

public export
IsYes : {type : Type} -> Dec type -> Type
IsYes dec = isYes dec = True

public export
IsYesExtract : {type : Type} -> {dec : Dec type} -> IsYes dec -> type
IsYesExtract {dec=(Yes x)} Refl = x
IsYesExtract {dec=(No _)} Refl impossible

public export
isYesExtract : {type : Type} -> (dec : Dec type) -> isYes dec = True -> type
isYesExtract (Yes x) Refl = x
isYesExtract (No _) Refl impossible

public export
isNoExtract : {type : Type} -> (dec : Dec type) -> isYes dec = False -> Not type
isNoExtract (Yes _) Refl impossible
isNoExtract (No isNo) _ = isNo

public export
DecPred : {A: Type} -> (pred: A -> Type) -> Type
DecPred pred = ((a : A) -> Dec (pred a))

public export
DecEqPred : (a: Type) -> Type
DecEqPred a = (x, x': a) -> Dec (x = x')

public export
decEqBool : {a: Type} -> DecEqPred a -> (x, x' : a) -> Bool
decEqBool deq x x' = isYes (deq x x')

public export
DecidableType : Type
DecidableType = DPair Type DecEqPred

public export
DecidableElem : DecidableType -> Type
DecidableElem type = fst type

public export
DecidablePred : {type : DecidableType} -> DecEqPred (DecidableElem type)
DecidablePred {type} = snd type

public export
listConsEq : {type : Type} -> {x, x' : type} -> {xs, xs' : List type} ->
             x = x' -> xs = xs' -> x :: xs = x' :: xs'
listConsEq elemEq listEq = rewrite elemEq in rewrite listEq in Refl

public export
DecEqList : {type : DecidableType} -> DecEqPred (List (DecidableElem type))
DecEqList [] [] = Yes Refl
DecEqList [] (x :: xs) = No (\eq => case eq of Refl impossible)
DecEqList (x :: xs) [] = No (\eq => case eq of Refl impossible)
DecEqList (x :: xs) (x' :: xs') =
  case (DecidablePred x x', DecEqList xs xs') of
    (Yes elemEq, Yes listEq) => Yes (listConsEq elemEq listEq)
    (No neq, _) => No (\eq => case eq of Refl => neq Refl)
    (_, No neq) => No (\eq => case eq of Refl => neq Refl)

public export
BoolCaseDec : Bool -> Type
BoolCaseDec b = Either (b = True) (b = False)

export
caseDecFromBool : (b: Bool) -> BoolCaseDec b
caseDecFromBool True = Left Refl
caseDecFromBool False = Right Refl

export
boolFromCaseDec : {b: Bool} -> BoolCaseDec b -> Bool
boolFromCaseDec bcd = case bcd of
                           Left Refl => True
                           Right Refl => False

public export
boolCaseDecIf : {A, B: Type} -> (b: Bool) ->
  (b = True -> A) -> (b = False -> B) -> if b then A else B
boolCaseDecIf b trueCase falseCase = case caseDecFromBool b of
  Left Refl => trueCase Refl
  Right Refl => falseCase Refl

public export
ifElimination : {t, t', result : Type} ->
  (b : Bool) ->
  (trueCase : b = True -> t -> result) ->
  (falseCase : b = False -> t' -> result) ->
  (test : if b then t else t') ->
  result
ifElimination True trueCase falseCase test = trueCase Refl test
ifElimination False trueCase falseCase test = falseCase Refl test

public export
boolCaseDecEither : (b: Bool) ->
                    {A: (b = True) -> Type} -> {B: (b = False) -> Type} ->
                    ((isTrue: b = True) -> A isTrue) ->
                    ((isFalse: b = False) -> B isFalse) ->
                    Either
                      (isTrue : b = True ** A isTrue)
                      (isFalse : b = False ** B isFalse)
boolCaseDecEither b trueCase falseCase = case caseDecFromBool b of
  Left Refl => Left (Refl ** trueCase Refl)
  Right Refl => Right (Refl ** falseCase Refl)

export
orElimination : {b, b': Bool} -> IsTrue (b || b') ->
                Either (IsTrue b) (IsTrue b')
orElimination {b=True} {b'=True} Refl = Left Refl
orElimination {b=True} {b'=False} Refl = Left Refl
orElimination {b=False} {b'=True} Refl = Right Refl
orElimination {b=False} {b'=False} Refl impossible

export
orIntroductionLeft : (b: Bool) -> {b': Bool} -> IsTrue b' -> IsTrue (b || b')
orIntroductionLeft True Refl = Refl
orIntroductionLeft False Refl = Refl

export
orIntroductionRight : {b: Bool} -> (b': Bool) -> IsTrue b -> IsTrue (b || b')
orIntroductionRight True Refl = Refl
orIntroductionRight False Refl = Refl

export
andElimination : {b, b': Bool} -> IsTrue (b && b') ->
                 ((IsTrue b), (IsTrue b'))
andElimination {b=True} {b'=True} Refl = (Refl, Refl)
andElimination {b=True} {b'=False} Refl impossible
andElimination {b=False} {b'=True} Refl impossible
andElimination {b=False} {b'=False} Refl impossible

export
andIntroduction : {b, b': Bool} -> (IsTrue b, IsTrue b') -> IsTrue (b && b')
andIntroduction (bTrue, bTrue') = case (bTrue, bTrue') of (Refl, Refl) => Refl

public export
isLeft : {A, B: Type} -> Either A B -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

public export
maybeCase : {a : Type} -> (m: Maybe a) ->
            Either (x : a ** m = Just x) (m = Nothing)
maybeCase (Just x) = Left (x ** Refl)
maybeCase Nothing = Right Refl

public export
maybeElimination : {a, b, c : Type} -> (m: Maybe a) ->
                   (case m of
                     Just x => b
                     Nothing => c) ->
                   Either (x : a ** (m = Just x, b)) (m = Nothing, c)
maybeElimination (Just x) c = Left (x ** (Refl, c))
maybeElimination Nothing c = Right (Refl, c)

public export
maybeMapElimination : {a: Type} ->
                      {ma: Maybe a} -> {ma': a -> Maybe a} -> {x : a} ->
                      (case ma of
                        Just y => ma' y
                        Nothing => Nothing) = Just x ->
                      (z : a ** ma' z = Just x)
maybeMapElimination {ma=(Just y)} eq = (y ** eq)
maybeMapElimination {ma=Nothing} Refl impossible

public export
maybePairElimination : {a, b : Type} -> (ma: Maybe a) -> (mb: Maybe b) ->
                       Either (p : (a, b) **
                                   (ma = Just (fst p), mb = Just (snd p)))
                              (Either (ma = Nothing) (mb = Nothing))
maybePairElimination (Just x) (Just y) = Left ((x, y) ** (Refl, Refl))
maybePairElimination Nothing _ = Right (Left Refl)
maybePairElimination (Just x) Nothing = Right (Right Refl)

public export IsNothing : {a: Type} -> Maybe a -> Type
IsNothing = IsTrue . isNothing

public export
IsJustIsTrue : {a : Type} -> (m : Maybe a) -> Type
IsJustIsTrue = IsTrue . isJust

public export
IsJustIsTrueElim : {a : Type} -> {m : Maybe a} -> IsJustIsTrue m -> a
IsJustIsTrueElim {m=(Just x)} Refl = x
IsJustIsTrueElim {m=Nothing} Refl impossible

public export
IsJustIsTrueRefl : {a : Type} -> {x : a} ->
                   (just : IsJustIsTrue (Just x)) ->
                   IsJustIsTrueElim {m=(Just x)} just = x
IsJustIsTrueRefl Refl = Refl

public export
isJustIsTrueDec : {a : Type} -> (m : Maybe a) ->
                  Dec (IsJustIsTrue m)
isJustIsTrueDec (Just _) = Yes Refl
isJustIsTrueDec Nothing = No (\eq => case eq of Refl impossible)

public export IsJustToTrue : {a : Type} -> {m : Maybe a} -> IsJust m ->
                             IsJustIsTrue m
IsJustToTrue ItIsJust = Refl

public export IsTrueToJust : {a : Type} -> {m : Maybe a} ->
                             IsTrue (isJust m) -> IsJust m
IsTrueToJust {m=(Just _)} Refl = ItIsJust
IsTrueToJust {m=Nothing} Refl impossible

public export EqJustToIsJust : {a : Type} -> {m : Maybe a} -> {x: a} ->
                               m = Just x -> IsJust m
EqJustToIsJust {m=(Just _)} Refl = ItIsJust
EqJustToIsJust {m=(Nothing)} Refl impossible

public export isJustElim : {a : Type} -> {m : Maybe a} ->
                           IsJustIsTrue m -> a
isJustElim {m=(Just x)} Refl = x
isJustElim {m=(Nothing)} Refl impossible

public export IsJustElim : {a : Type} -> {m : Maybe a} ->
                           IsJust m -> a
IsJustElim {m=(Just x)} ItIsJust = x
IsJustElim {m=(Nothing)} ItIsJust impossible

public export IsJustElimElim : {a : Type} -> (x : a) ->
                               IsJustElim (ItIsJust {x}) = x
IsJustElimElim _ = Refl

public export
NotPred : {A: Type} -> (p: A -> Type) -> Type
NotPred p = (a: A) -> Not (p a)

public export
NotDec : {A: Type} -> (p: A -> Type) -> Type
NotDec p = Dec (NotPred p)

public export
notDec : {A: Type} -> {pred: A -> Type} -> (p : (a: A) -> Dec (pred a)) ->
         ((a: A) -> Dec (Not (pred a)))
notDec p a = case p a of
  Yes predTrue => No (\notPred => notPred predTrue)
  No predFalse => Yes predFalse

public export
IsGodelNumbering : {type : Type} -> (type -> Nat) -> Type
IsGodelNumbering {type} g = (inv : (Nat -> Maybe type) **
                             ((x : type) -> inv (g x) = Just x))

public export
GodelNumbering : Type -> Type
GodelNumbering type = DPair (type -> Nat) IsGodelNumbering

public export
GodelNumbered : Type
GodelNumbered = DPair Type GodelNumbering

public export
GodelType : GodelNumbered -> Type
GodelType = fst

public export
numberingDecEq : {type : Type} -> GodelNumbering type -> DecEqPred type
numberingDecEq (g ** (inv ** isInverse)) x x' with (decEq (g x) (g x'))
  numberingDecEq (g ** (inv ** isInverse)) x x' | Yes eq =
    let
      invx = isInverse x
      invx' = isInverse x'
      eqx = replace {p=(\y => inv y = Just x)} eq invx
      eqx' = replace {p=(\y => y = Just x')} eqx invx'
    in
    Yes (justInjective eqx')
  numberingDecEq (g ** (inv ** isInverse)) x x' | No neq =
    No (\eq => case eq of Refl => neq Refl)

public export
godelDecEq : (type : GodelNumbered) -> DecEqPred (fst type)
godelDecEq type = numberingDecEq (snd type)

public export
uip : {a : Type} -> {x, y : a} -> (eq, eq' : x = y) -> eq = eq'
uip Refl Refl = Refl

public export
rewrite_uip : {a : Type} -> {x, y : a} ->
  {p : (eq : x = y) -> Type} ->
  {f : (eq : x = y) -> p eq} ->
  {eq, eq' : x = y} ->
  f eq = f eq'
rewrite_uip {eq} {eq'} = rewrite (uip eq eq') in Refl

public export
IsYesUnique : {type : Type} -> {dec : Dec type} -> (yes, yes' : IsYes dec) ->
  yes = yes'
IsYesUnique yes yes' = uip yes yes'

public export
YesDPairInjective : {a : Type} -> {b : a -> Type} ->
  {dec : (x : a) -> Dec (b x)} -> {x : a} ->
  {d, d' : DPair a (\x => IsYes (dec x))} -> fst d = fst d' -> d = d'
YesDPairInjective =
  UniqueHeterogeneousDPairInjective (\_, yes, yes' => IsYesUnique yes yes')
