module RefinedSExp.RefinedSExp

import public RefinedSExp.SExp

%default total

public export
SDecisionP : {atom : Type} -> (predicate : SPredicate atom) -> Type
SDecisionP predicate = (x : SExp atom) -> Dec (predicate x)

public export
SLDecisionP : {atom : Type} -> (predicate : SLPredicate atom) -> Type
SLDecisionP predicate = (l : SList atom) -> Dec (predicate l)

prefix 11 $?
public export
($?) : {atom : Type} -> (predicate : SPredicate atom) -> Type
($?) = SDecisionP

prefix 11 $:?
public export
($:?) : {atom : Type} -> (predicate : SLPredicate atom) -> Type
($:?) = SLDecisionP

public export
SatisfiesSPred : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $? predicate) -> SExp atom -> Type
SatisfiesSPred decide x = IsYes (decide x)

prefix 11 $&
public export
($&) : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $? predicate) -> SExp atom -> Type
($&) = SatisfiesSPred

public export
SatisfiesSLPred : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:? predicate) -> SList atom -> Type
SatisfiesSLPred decide l = IsYes (decide l)

prefix 11 $:&
public export
($:&) : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:? predicate) -> SList atom -> Type
($:&) = SatisfiesSLPred

prefix 11 $~
public export
($~) : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $? predicate) -> Type
($~) decide = DPair (SExp atom) (SatisfiesSPred decide)

prefix 11 $:~
public export
($:~) : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:? predicate) -> Type
($:~) decide = DPair (SList atom) (SatisfiesSLPred decide)

-- Refined S-expression.
public export
RExp : {atom : Type} -> {predicate : SPredicate atom} ->
  (decide : $? predicate) -> Type
RExp decide = DPair (SExp atom) ($& decide)

-- Refined S-list.
public export
RList : {atom : Type} -> {predicate : SLPredicate atom} ->
  (decide : $:? predicate) -> Type
RList decide = DPair (SList atom) ($:& decide)

RExpProofInsensitive : {atom : Type} -> {predicate : SPredicate atom} ->
  {decide : $? predicate} -> {rx, rx' : RExp decide} -> (fst rx = fst rx') ->
  rx = rx'
RExpProofInsensitive {decide} eq = YesDPairInjective {dec=decide} eq
