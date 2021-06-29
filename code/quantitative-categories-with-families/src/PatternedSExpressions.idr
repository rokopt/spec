module PatternedSExpressions

import Decidable.Equality

%default total

data PrimitiveType : Type where
  PrimTypeBool : PrimitiveType
  PrimTypeNat : PrimitiveType
  PrimTypeString : PrimitiveType

-- Haskell can just derive this.
primTypeEq : (primType, primType' : PrimitiveType) -> Dec (primType = primType')
primTypeEq PrimTypeBool PrimTypeBool = Yes Refl
primTypeEq PrimTypeBool PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeBool PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeNat PrimTypeNat = Yes Refl
primTypeEq PrimTypeNat PrimTypeString = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeBool = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeNat = No (\eq => case eq of Refl impossible)
primTypeEq PrimTypeString PrimTypeString = Yes Refl

data PrimitiveExp : PrimitiveType -> Type where
  PrimExpBool : Bool -> PrimitiveExp PrimTypeBool
  PrimExpNat : Nat -> PrimitiveExp PrimTypeNat
  PrimExpString : String -> PrimitiveExp PrimTypeString

primExpEq : {primType : PrimitiveType} ->
  (primExp, primExp' : PrimitiveExp primType) -> Dec (primExp = primExp')
primExpEq (PrimExpBool b) (PrimExpBool b') = case decEq b b' of
  Yes Refl => Yes Refl
  No neq => No (\eq => case eq of Refl => neq Refl)
primExpEq (PrimExpBool b) (PrimExpNat n) impossible
primExpEq (PrimExpBool b) (PrimExpString s) impossible
primExpEq (PrimExpNat n) (PrimExpBool b) impossible
primExpEq (PrimExpNat n) (PrimExpNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No (\eq => case eq of Refl => neq Refl)
primExpEq (PrimExpNat n) (PrimExpString s) impossible
primExpEq (PrimExpString s) (PrimExpBool b) impossible
primExpEq (PrimExpString s) (PrimExpNat n) impossible
primExpEq (PrimExpString s) (PrimExpString s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No (\eq => case eq of Refl => neq Refl)

mutual
  data SExp : Type where
    SAtom : {primType : PrimitiveType} -> PrimitiveExp primType -> SExp
    SList : SExpList -> SExp

  SExpList : Type
  SExpList = List SExp

mutual
  sexpEq : (sexp, sexp' : SExp) -> Dec (sexp = sexp')
  sexpEq (SAtom {primType} exp) (SAtom {primType=primType'} exp') =
    case primTypeEq primType primType' of
      Yes Refl => case primExpEq exp exp' of
        Yes Refl => Yes Refl
        No neq => No (\eq => case eq of Refl => neq Refl)
      No neq => No (\eq => case eq of Refl => neq Refl)
  sexpEq (SAtom _) (SList _) = No (\eq => case eq of Refl impossible)
  sexpEq (SList _) (SAtom _) = No (\eq => case eq of Refl impossible)
  sexpEq (SList sexpList) (SList sexpList') =
    case sexpListEq sexpList sexpList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  sexpListEq : (sexpList, sexpList' : SExpList) -> Dec (sexpList = sexpList')
  sexpListEq = let _ = sexpListDecEq in decEq

  [sexpDecEq] DecEq SExp where
    decEq = sexpEq

  [sexpListDecEq] DecEq SExpList where
    decEq = sexpListEq

mutual
  data Pattern : Type where
    DefaultPat : Pattern
    PrimPat : PrimitiveType -> Pattern
    ProductPat : List Pattern -> Pattern
    SumPat : List Pattern -> Pattern

  PatternList : Type
  PatternList = List Pattern

mutual
  patternEq : (pattern, pattern' : Pattern) -> Dec (pattern = pattern')
  patternEq DefaultPat DefaultPat = Yes Refl
  patternEq DefaultPat (PrimPat _) = No (\eq => case eq of Refl impossible)
  patternEq DefaultPat (ProductPat _) = No (\eq => case eq of Refl impossible)
  patternEq DefaultPat (SumPat _) = No (\eq => case eq of Refl impossible)
  patternEq (PrimPat _) DefaultPat = No (\eq => case eq of Refl impossible)
  patternEq (PrimPat primType) (PrimPat primType') =
    case primTypeEq primType primType' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq (PrimPat _) (ProductPat _) = No (\eq => case eq of Refl impossible)
  patternEq (PrimPat _) (SumPat _) = No (\eq => case eq of Refl impossible)
  patternEq (ProductPat _) DefaultPat = No (\eq => case eq of Refl impossible)
  patternEq (ProductPat _) (PrimPat _) = No (\eq => case eq of Refl impossible)
  patternEq (ProductPat patternList) (ProductPat patternList') =
    case patternListEq patternList patternList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)
  patternEq (ProductPat _) (SumPat _) = No (\eq => case eq of Refl impossible)
  patternEq (SumPat _) DefaultPat = No (\eq => case eq of Refl impossible)
  patternEq (SumPat _) (PrimPat _) = No (\eq => case eq of Refl impossible)
  patternEq (SumPat _) (ProductPat _) = No (\eq => case eq of Refl impossible)
  patternEq (SumPat patternList) (SumPat patternList') =
    case patternListEq patternList patternList' of
      Yes Refl => Yes Refl
      No neq => No (\eq => case eq of Refl => neq Refl)

  patternListEq :(patternList, patternList' : PatternList) ->
    Dec (patternList = patternList')
  patternListEq = let _ = patternListDecEq in decEq

  [patternDecEq] DecEq Pattern where
    decEq = patternEq

  [patternListDecEq] DecEq PatternList where
    decEq = patternListEq

mutual
  data MatchesExp : Pattern -> SExp -> Type where
    MatchesDefault : (sexp : SExp) -> MatchesExp DefaultPat sexp
    MatchesPrim :
      (primType : PrimitiveType) -> (primExp : PrimitiveExp primType) ->
      MatchesExp (PrimPat primType) (SAtom primExp)
    MatchesProduct : {patternList : PatternList} -> {sexpList : SExpList} ->
      MatchesList patternList sexpList ->
      MatchesExp (ProductPat patternList) (SList sexpList)
    MatchesSum : {patternList : PatternList} -> {sexp : SExp} ->
      MatchesSome patternList sexp ->
      MatchesExp (ProductPat patternList) sexp

  data MatchesList : PatternList -> SExpList -> Type where
    MatchesNil : MatchesList [] []
    MatchesCons :
      {headPat : Pattern} -> {headSExp : SExp} ->
      MatchesExp headPat headSExp ->
      {tailPat : PatternList} -> {tailSExp : SExpList} ->
      MatchesList tailPat tailSExp ->
      MatchesList (headPat :: tailPat) (headSExp :: tailSExp)

  data MatchesSome : PatternList -> SExp -> Type where
    MatchesHead :
      {headPat : Pattern} -> {tailPat : PatternList} -> {sexp : SExp} ->
      MatchesExp headPat sexp ->
      MatchesSome (headPat :: tailPat) sexp
    MatchesTail :
      {headPat : Pattern} -> {tailPat : PatternList} -> {sexp : SExp} ->
      MatchesSome tailPat sexp ->
      MatchesSome (headPat :: tailPat) sexp
