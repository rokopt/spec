module RefinedSExp.AlgebraicSExp

import Library.FunctionsAndRelations
import Category.ComputableCategories

%default total

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
SPred atom = !- (SExp atom)

public export
SLPred : (atom : Type) -> Type
SLPred atom = !- (SList atom)

public export
record SExpEliminatorSig
  {0 atom : Type} (0 sp : SPred atom) (0 lp : SLPred atom)
  where
    constructor SExpEliminatorArgs
    expElim : (a : atom) -> (l : SList atom) -> lp l -> sp (a $* l)
    nilElim : lp []
    consElim : (x : SExp atom) -> (l : SList atom) ->
      sp x -> lp l -> lp (x :: l)

mutual
  public export
  sexpEliminator :
    {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SExp atom ~> sp
  sexpEliminator signature (a $* l) =
    expElim signature a l (slistEliminator signature l)

  public export
  slistEliminator :
    {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
    (signature : SExpEliminatorSig sp lp) ->
    SList atom ~> lp
  slistEliminator signature [] =
    nilElim signature
  slistEliminator signature (x :: l) =
    consElim signature x l
      (sexpEliminator signature x) (slistEliminator signature l)

public export
sexpEliminators :
  {0 atom : Type} -> {0 sp : SPred atom} -> {0 lp : SLPred atom} ->
  (signature : SExpEliminatorSig sp lp) ->
  (SExp atom ~> sp, SList atom ~> lp)
sexpEliminators signature =
  (sexpEliminator signature, slistEliminator signature)

public export
SExpInductivePredSig : (0 atom : Type) -> Type
SExpInductivePredSig atom = SExpEliminatorSig {atom} (\_ => Type) (\_ => Type)

public export
data RefinedAtom : Type where

public export
RefinedSExp : Type
RefinedSExp = SExp RefinedAtom

public export
RefinedSList : Type
RefinedSList = SList RefinedAtom

mutual
  public export
  data RefinedObject : (representation : RefinedSExp) -> Type where

  public export
  data RefinedMorphism :
    (representation, domainRep, codomainRep : RefinedSExp) -> Type where

  public export
  data RefinedContract :
    (representation, subjectMorphismRep : RefinedSExp) -> Type where

  public export
  sexpAsObject : (representation : RefinedSExp) ->
    Maybe (RefinedObject representation)
  sexpAsObject _ = Nothing

  public export
  sexpAsMorphism : (representation, domainRep, codomainRep : RefinedSExp) ->
    Maybe (RefinedMorphism representation domainRep codomainRep)
  sexpAsMorphism _ _ _ = Nothing

  public export
  sexpAsContract : (representation, subjectMorphismRep : RefinedSExp) ->
    Maybe (RefinedContract representation subjectMorphismRep)
  sexpAsContract _ _ = Nothing

  export
  sexpAsObjectComplete : {representation : RefinedSExp} ->
    (obj : RefinedObject representation) ->
    sexpAsObject representation = Just obj
  sexpAsObjectComplete _ impossible

  export
  sexpAsMorphismComplete :
    {representation, domainRep, codomainRep : RefinedSExp} ->
    (morphism : RefinedMorphism representation domainRep codomainRep) ->
    sexpAsMorphism representation = Just morphism
  sexpAsMorphismComplete _ impossible

  export
  sexpAsContractComplete : {representation, subjectMorphismRep : RefinedSExp} ->
    (morphism : RefinedContract representation subjectMorphismRep) ->
    sexpAsContract representation = Just morphism
  sexpAsContractComplete _ impossible
