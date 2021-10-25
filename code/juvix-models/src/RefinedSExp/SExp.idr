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

infixr 7 :~:
public export
data Telescope :
  {0 fieldRepresentationType : Type} ->
  (0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type) ->
  (representation : List fieldRepresentationType) ->
  (previousFields : List fieldRepresentationType) ->
  Type where
    (|~|) :
      {0 fieldRepresentationType : Type} ->
      {0 fieldType :
        fieldRepresentationType -> List fieldRepresentationType -> Type} ->
      {previousFields : List fieldRepresentationType} ->
      Telescope fieldType [] previousFields
    (:~:) :
      {0 fieldRepresentationType : Type} ->
      {0 fieldType :
        fieldRepresentationType -> List fieldRepresentationType -> Type} ->
      {previousFields : List fieldRepresentationType} ->
      {headRep : fieldRepresentationType} ->
      {tailRep : List fieldRepresentationType} ->
      fieldType headRep previousFields ->
      Telescope fieldType tailRep (previousFields ++ [headRep]) ->
      Telescope fieldType (headRep :: tailRep) previousFields

prefix 11 !~!
public export
(!~!) : {0 fieldRepresentationType : Type} ->
  {0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  {representation : fieldRepresentationType} ->
  {previousFields : List fieldRepresentationType} ->
  fieldType representation previousFields ->
  Telescope fieldType [representation] previousFields
(!~!) field = field :~: (|~|)

infixr 7 :~!
public export
(:~!) : {0 fieldRepresentationType : Type} ->
  {0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  {headRep, tailRep : fieldRepresentationType} ->
  {previousFields : List fieldRepresentationType} ->
  fieldType headRep previousFields ->
  fieldType tailRep (previousFields ++ [headRep]) ->
  Telescope fieldType [headRep, tailRep] previousFields
head :~! tail = head :~: !~! tail

public export
TelescopeTypeN :
  {0 fieldRepresentationType : Type} ->
  {fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  (representation : List fieldRepresentationType) ->
  (previousFields : List fieldRepresentationType) ->
  (n : Nat) ->
  {auto ok : InBounds n representation} ->
  Type
TelescopeTypeN {fieldType} representation previousFields n =
  fieldType (index n representation {ok})
    (previousFields ++ take n representation)

infixr 8 @~
public export
(@~) :
  {0 fieldRepresentationType : Type} ->
  {0 fieldType :
    fieldRepresentationType -> List fieldRepresentationType -> Type} ->
  {representation : List fieldRepresentationType} ->
  {previousFields : List fieldRepresentationType} ->
  Telescope fieldType representation previousFields ->
  (n : Nat) ->
  {auto ok : InBounds n representation} ->
  TelescopeTypeN {fieldType} representation previousFields n {ok}
(@~) {representation=(headRep :: _)} (head :~: _) Z {ok=InFirst} =
  rewrite appendNilRightNeutral previousFields in
  head
(@~) {representation=(headRep :: tailRep)}
  (field :~: telescope) (S n) {ok=(InLater _)} =
    rewrite appendAssociative previousFields [headRep] (take n tailRep) in
    telescope @~ n

public export
SAlgAtom : Type
SAlgAtom = Nat
{-
data SAlgAtom : Type where
  SAlgSort : Nat -> SAlgAtom
  SAlgParam : Nat -> SAlgAtom
  -}

public export
SAlgExp : Type
SAlgExp = SExp SAlgAtom

public export
SAlgList : Type
SAlgList = SList SAlgAtom

mutual
  public export
  SortSignatureList :
    (representation : List SAlgList) -> (sortSigsInContext : List SAlgList) ->
    Type
  SortSignatureList = Telescope SortSignature

  public export
  SortSignature : (representation : SAlgList) ->
    (sortSigsInContext : List SAlgList) ->
    Type
  SortSignature representation sortSigsInContext =
    Telescope (Refinement sortSigsInContext) representation []

  public export
  data Refinement :
    (sortSigsInContext : List SAlgList) ->
    (representation : SAlgExp) ->
    (paramsInContext : SAlgList) ->
    Type where
      ApplySort : (sortSigsInContext : List SAlgList) ->
        (paramsInContext : SAlgList) ->
        (sort : Nat) -> (sortParams : SAlgList) ->
        {auto ok : InBounds sort sortSigsInContext} ->
        {auto matches : MatchesSortSignature
          (take sort sortSigsInContext) paramsInContext
          (index sort sortSigsInContext {ok}) sortParams} ->
        Refinement
          sortSigsInContext (sort $* sortParams) paramsInContext

  public export
  data MatchesSortSignature :
    (sortSigsInContext : List SAlgList) ->
    (paramsInContext : SAlgList) ->
    (sortSig : SAlgList) ->
    (params : SAlgList) ->
    Type where
      MatchesNil :
        {sortSigsInContext : List SAlgList} -> {paramsInContext : SAlgList} ->
        MatchesSortSignature sortSigsInContext paramsInContext [] []
      MatchesCons :
        {sortSigsInContext : List SAlgList} -> {paramsInContext : SAlgList} ->
        {sigHead, paramHead : SAlgExp} -> {sigTail, paramTail : SAlgList} ->
        MatchesSortParam sortSigsInContext paramsInContext
          sigHead paramHead ->
        MatchesSortSignature sortSigsInContext paramsInContext
          sigTail paramTail ->
        MatchesSortSignature
          sortSigsInContext paramsInContext
            (sigHead :: sigTail) (paramHead :: paramTail)

  public export
  data MatchesSortParam :
    (sortSigsInContext : List SAlgList) ->
    (paramsInContext : SAlgList) ->
    (sig : SAlgExp) ->
    (param : SAlgExp) ->
    Type where
