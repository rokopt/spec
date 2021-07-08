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

prefix 11 <$
public export
(<$) : {atom : Type} -> SExp atom -> atom
(<$) (a $: _) = a

prefix 11 >$
public export
(>$) : {atom : Type} -> SExp atom -> SList atom
(>$) (_ $: l) = l

public export
ListToSListToListEq : {atom : Type} -> (l : List (SExp atom)) ->
  ($>*) ($<* l) = l
ListToSListToListEq [] = Refl
ListToSListToListEq (x :: l) = cong ((::) x) (ListToSListToListEq l)

public export
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

public export
mapSLForAll : {atom : Type} ->
  {sp, sp' : SPredicate atom} -> {l : SList atom} ->
  (f : (x : SExp atom) -> sp x -> sp' x) ->
  SLForAll sp l -> SLForAll sp' l
mapSLForAll f SLForAllEmpty = SLForAllEmpty
mapSLForAll f (SLForAllCons head forAllTail) =
  SLForAllCons (f _ head) (mapSLForAll f forAllTail)

public export
SLForAllUnique : {atom : Type} -> {sp : SPredicate atom} -> {l : SList atom} ->
  (forAll, forAll' : SLForAll sp l) ->
  ((x : SExp atom) -> (spx, spx' : sp x) -> spx = spx') ->
  forAll = forAll'
SLForAllUnique SLForAllEmpty SLForAllEmpty spUnique = Refl
SLForAllUnique SLForAllEmpty (SLForAllCons _ _) _ impossible
SLForAllUnique (SLForAllCons _ _) SLForAllEmpty _ impossible
SLForAllUnique (SLForAllCons head tail) (SLForAllCons head' tail') spUnique =
  case spUnique _ head head' of
    Refl => cong (SLForAllCons head) (SLForAllUnique tail tail' spUnique)

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
sIndForAll forAllElim =
  sInd {sp} {lp=(SLForAll sp)} forAllElim SLForAllEmpty (\_, _ => SLForAllCons)

public export
sExpIndForAll :
  {atom : Type} -> {sp : SPredicate atom} ->
  (forAllElim :
    (a : atom) -> (l : SList atom) ->
    SLForAll sp l -> sp (a $: l)) ->
  (x : SExp atom) -> sp x
sExpIndForAll forAllElim = fst (sIndForAll forAllElim)

public export
sListIndForAll :
  {atom : Type} -> {sp : SPredicate atom} ->
  (forAllElim :
    (a : atom) -> (l : SList atom) ->
    SLForAll sp l -> sp (a $: l)) ->
  (l : SList atom) -> SLForAll sp l
sListIndForAll forAllElim = snd (sIndForAll forAllElim)

public export
sTransform :
  {atom, atom' : Type} ->
  (expTransform : atom -> (l : SList atom) -> SLForAll (\_ => SExp atom') l ->
    SExp atom') ->
  (SExp atom -> SExp atom', (l : SList atom) -> SLForAll (\_ => SExp atom') l)
sTransform {atom} {atom'} = sIndForAll {atom} {sp=(\_ => SExp atom')}

public export
sExpTransform :
  {atom, atom' : Type} ->
  (expTransform : atom -> (l : SList atom) -> SLForAll (\_ => SExp atom') l ->
    SExp atom') ->
  SExp atom -> SExp atom'
sExpTransform = fst . sTransform

public export
sListTransform :
  {atom, atom' : Type} ->
  (expTransform : atom -> (l : SList atom) -> SLForAll (\_ => SExp atom') l ->
    SExp atom') ->
  (l : SList atom) -> SLForAll (\_ => SExp atom') l
sListTransform = snd . sTransform

public export
SDepPred : {atom : Type} -> SPredicate atom -> Type
SDepPred {atom} pred = (x : SExp atom) -> pred x -> Type

public export
SDepPredPair : {atom : Type} -> {sp : SPredicate atom} ->
  SDepPred sp -> SPredicate atom
SDepPredPair {sp} sdp = \x => (spx : sp x ** sdp x spx)

public export
SLDepPred : {atom : Type} -> SLPredicate atom -> Type
SLDepPred {atom} pred = (l : SList atom) -> pred l -> Type

public export
SLDepPredPair : {atom : Type} -> {lp : SLPredicate atom} ->
  SLDepPred lp -> SLPredicate atom
SLDepPredPair {lp} ldp = \l => (lpl : lp l ** ldp l lpl)

public export
sDepInd :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  {sdp : SDepPred sp} -> {ldp : SLDepPred lp} ->
  {expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)} ->
  {nilElim : lp ($|)} ->
  {consElim :
    (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)} ->
  (depExpElim : (a : atom) -> (l : SList atom) ->
    (lpl : lp l) -> (lpl = sListInd expElim nilElim consElim l) ->
    ldp l lpl ->
    sdp (a $:l) (expElim a l lpl)) ->
  (depNilElim : nilElim = sListInd expElim nilElim consElim ($|) ->
    ldp ($|) nilElim) ->
  (depConsElim : (x : SExp atom) -> (l: SList atom) ->
    (spx : sp x) -> (lpl : lp l) ->
    (spx = sExpInd expElim nilElim consElim x) ->
    (lpl = sListInd expElim nilElim consElim l) ->
    sdp x spx ->
    ldp l lpl ->
    ldp (x $+ l) (consElim x l spx lpl)) ->
  ((x : SExp atom) -> sdp x (sExpInd expElim nilElim consElim x),
   (l : SList atom) -> ldp l (sListInd expElim nilElim consElim l))
sDepInd {expElim} {nilElim} {consElim} depExpElim depNilElim depConsElim =
  sInd
    (\a, l => depExpElim a l (sListInd {sp} expElim nilElim consElim l) Refl)
    (depNilElim Refl)
    (\x, l =>
      depConsElim x l
        (sExpInd {sp} {lp} expElim nilElim consElim x)
        (sListInd {sp} {lp} expElim nilElim consElim l)
        Refl Refl)

public export
data SLForAllDep : {atom : Type} -> {sp : SPredicate atom} ->
    SDepPred sp -> SLDepPred (SLForAll sp) where
  SLForAllDepEmpty : {atom : Type} -> {sp : SPredicate atom} ->
    {sdp : SDepPred sp} -> SLForAllDep sdp ($|) SLForAllEmpty
  SLForAllDepCons : {atom : Type} -> {sp : SPredicate atom} ->
    {sdp : SDepPred sp} ->
    {x : SExp atom} -> {l : SList atom} ->
    {spx : sp x} -> {splForAll : SLForAll sp l} ->
    sdp x spx -> SLForAllDep sdp l splForAll ->
    SLForAllDep sdp (x $+ l) (SLForAllCons spx splForAll)

public export
SLPairsFst : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  (forAll : SLForAll (SDepPredPair sdp) l) ->
  SLForAll sp l
SLPairsFst SLForAllEmpty = SLForAllEmpty
SLPairsFst (SLForAllCons sdpx sdpl) = SLForAllCons (fst sdpx) (SLPairsFst sdpl)

public export
SLPairsSnd : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  (forAll : SLForAll (SDepPredPair sdp) l) ->
  SLForAllDep sdp l (SLPairsFst forAll)
SLPairsSnd SLForAllEmpty = SLForAllDepEmpty
SLPairsSnd {sdp} (SLForAllCons sdpx sdpl) =
  SLForAllDepCons {sdp} (snd sdpx) (SLPairsSnd {sdp} sdpl)

public export
SLPairsToForAllDep : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  (forAll : SLForAll (SDepPredPair sdp) l) ->
  SLForAllDep sdp l (SLPairsFst forAll)
SLPairsToForAllDep SLForAllEmpty = SLForAllDepEmpty
SLPairsToForAllDep {sdp} (SLForAllCons (_ ** head) forAllTail) =
  SLForAllDepCons head (SLPairsToForAllDep {sdp} forAllTail)

public export
SLForAllDepToPairs : {atom : Type} -> {sp : SPredicate atom} ->
  {sdp : SDepPred sp} -> {l : SList atom} ->
  {forAll : SLForAll sp l} -> SLForAllDep sdp l forAll ->
  SLForAll (SDepPredPair sdp) l
SLForAllDepToPairs SLForAllDepEmpty = SLForAllEmpty
SLForAllDepToPairs (SLForAllDepCons head forAllTail) =
  SLForAllCons (_ ** head) (SLForAllDepToPairs forAllTail)

public export
sDepIndForAll :
  {atom : Type} -> {sp : SPredicate atom} -> {sdp : SDepPred sp} ->
  {forAllElim :
    (a : atom) -> (l : SList atom) ->
    SLForAll sp l -> sp (a $: l)} ->
  (depForAllElim : (a : atom) -> (l : SList atom) ->
    (lpl : SLForAll sp l) -> lpl = sListIndForAll forAllElim l ->
    SLForAllDep sdp l lpl ->
    sdp (a $: l) (forAllElim a l lpl)) ->
  ((x : SExp atom) -> sdp x (sExpIndForAll forAllElim x),
   (l : SList atom) -> SLForAllDep sdp l (sListIndForAll forAllElim l))
sDepIndForAll {forAllElim} depForAllElim =
  sDepInd {sp} {lp=(SLForAll sp)}
    {sdp}
    {ldp=(SLForAllDep sdp)}
    {expElim=forAllElim}
    {nilElim=SLForAllEmpty}
    {consElim=(\_, _ => SLForAllCons)}
    depForAllElim
    (\_ => SLForAllDepEmpty)
    (\_, _, _, _, _, _ => SLForAllDepCons)

public export
SDPair : {atom : Type} -> SPredicate atom -> Type
SDPair {atom} pred = DPair (SExp atom) pred

prefix 11 <:$
public export
(<:$) : {atom : Type} -> {pred : SPredicate atom} -> SDPair pred -> SExp atom
(<:$) (x ** _) = x

prefix 11 >:$
public export
(>:$) : {atom : Type} -> {pred : SPredicate atom} -> (dx : SDPair pred) ->
  pred (<:$ dx)
(>:$) (_ ** spx) = spx

public export
SLDPair : {atom : Type} -> SLPredicate atom -> Type
SLDPair {atom} pred = DPair (SList atom) pred

prefix 11 <+$
public export
(<+$) : {atom : Type} -> {pred : SLPredicate atom} -> SLDPair pred -> SList atom
(<+$) (l ** _) = l

prefix 11 >+$
public export
(>+$) : {atom : Type} -> {pred : SLPredicate atom} -> (dl : SLDPair pred) ->
  pred (<+$ dl)
(>+$) (_ ** lpl) = lpl

public export
SDPairPred : {atom : Type} -> SPredicate atom -> Type
SDPairPred pred = SDPair pred -> Type

public export
SLDPairPred : {atom : Type} -> SLPredicate atom -> Type
SLDPairPred pred = SLDPair pred -> Type

-- Construct a dependent function on dependent pairs.
public export
sdpairInd :
  {atom : Type} -> {sp : SPredicate atom} -> {lp : SLPredicate atom} ->
  {sdp : SDPairPred sp} -> {ldp : SLDPairPred lp} ->
  {expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $: l)} ->
  {nilElim : lp ($|)} ->
  {consElim :
    (x : SExp atom) -> (l : SList atom) -> sp x -> lp l -> lp (x $+ l)} ->
  (depExpElim : (a : atom) -> (l : SList atom) ->
    (lpl : lp l) -> (lpl = sListInd expElim nilElim consElim l) ->
    ldp (l ** lpl) ->
    sdp (a $: l ** expElim a l lpl)) ->
  (depNilElim : nilElim = sListInd expElim nilElim consElim ($|) ->
    ldp (($|) ** nilElim)) ->
  (depConsElim : (x : SExp atom) -> (l: SList atom) ->
    (spx : sp x) -> (lpl : lp l) ->
    (spx = sExpInd expElim nilElim consElim x) ->
    (lpl = sListInd expElim nilElim consElim l) ->
    sdp (x ** spx) ->
    ldp (l ** lpl) ->
    ldp (x $+ l ** consElim x l spx lpl)) ->
  ((x : SExp atom) -> sdp (x ** sExpInd expElim nilElim consElim x),
   (l : SList atom) -> ldp (l ** sListInd expElim nilElim consElim l))
sdpairInd {sdp} {ldp} =
  sDepInd {sdp=(\x, spx => sdp (x ** spx))} {ldp=(\l, lpl => ldp (l ** lpl))}
