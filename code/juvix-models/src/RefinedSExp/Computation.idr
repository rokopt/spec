module RefinedSExp.Computation

import public Library.FunctionsAndRelations
import public Library.Decidability
import public Library.List
import public Category.ComputableCategories
import public RefinedSExp.SExp

%default total

public export
data Keyword : Type where
  Fail : Keyword
  Compose : Keyword
  Identity : Keyword
  Const : Keyword
  Tuple : Keyword
  Project : Keyword
  Enum : Keyword
  Inject : Keyword
  Eval : Keyword
  Curry : Keyword
  Fix : Keyword
  Cofix : Keyword

public export
keywordToString : Keyword -> String
keywordToString Fail = "Fail"
keywordToString Compose = "Compose"
keywordToString Identity = "Identity"
keywordToString Const = "Const"
keywordToString Tuple = "Tuple"
keywordToString Project = "Project"
keywordToString Enum = "Enum"
keywordToString Inject = "Inject"
keywordToString Eval = "Eval"
keywordToString Curry = "Curry"
keywordToString Fix = "Fix"
keywordToString Cofix = "Cofix"

public export
Show Keyword where
  show k = ":" ++ keywordToString k

public export
kEncode : Keyword -> Nat
kEncode Fail = 0
kEncode Compose = 1
kEncode Identity = 2
kEncode Const = 3
kEncode Tuple = 4
kEncode Project = 5
kEncode Enum = 6
kEncode Inject = 7
kEncode Eval = 8
kEncode Curry = 9
kEncode Fix = 10
kEncode Cofix = 11

public export
kDecode : Nat -> Keyword
kDecode 0 = Fail
kDecode 1 = Compose
kDecode 2 = Identity
kDecode 3 = Const
kDecode 4 = Tuple
kDecode 5 = Project
kDecode 6 = Enum
kDecode 7 = Inject
kDecode 8 = Eval
kDecode 9 = Curry
kDecode 10 = Fix
kDecode 11 = Cofix
kDecode _ = Fail

export
kDecodeIsLeftInverse :
  IsLeftInverseOf Computation.kEncode Computation.kDecode
kDecodeIsLeftInverse Fail = Refl
kDecodeIsLeftInverse Compose = Refl
kDecodeIsLeftInverse Identity = Refl
kDecodeIsLeftInverse Const = Refl
kDecodeIsLeftInverse Tuple = Refl
kDecodeIsLeftInverse Project = Refl
kDecodeIsLeftInverse Enum = Refl
kDecodeIsLeftInverse Inject = Refl
kDecodeIsLeftInverse Eval = Refl
kDecodeIsLeftInverse Curry = Refl
kDecodeIsLeftInverse Fix = Refl
kDecodeIsLeftInverse Cofix = Refl

export
kEncodeIsInjective : IsInjective Computation.kEncode
kEncodeIsInjective =
  leftInverseImpliesInjective kEncode {g=kDecode} kDecodeIsLeftInverse

public export
KInjection : Injection Keyword Nat
KInjection = (kEncode ** kEncodeIsInjective)

public export
KCountable : Countable
KCountable = (Keyword ** KInjection)

public export
kDecEq : DecEqPred Keyword
kDecEq = countableEq KCountable

public export
DecEq Keyword where
  decEq = kDecEq

public export
Eq Keyword using decEqToEq where
  (==) = (==)

public export
Ord Keyword where
  k < k' = kEncode k < kEncode k'

-- | Data with no structure besides a decidable equality -- a "type of
-- | individuals" for particular use when _interpreting_ expressions as
-- | representing computable functions.
public export
data Data : Type where
  DReflectedKeyword : Keyword -> Data
  DNat : Nat -> Data
  DString : String -> Data

public export
Show Data where
  show (DReflectedKeyword k) = "~" ++ keywordToString k
  show (DNat n) = show n
  show (DString s) = "'" ++ s

export
dDecEq : DecEqPred Data
dDecEq (DReflectedKeyword k) (DReflectedKeyword k') = case decEq k k' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
dDecEq (DReflectedKeyword _) (DNat _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DReflectedKeyword _) (DString _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DNat _) (DReflectedKeyword _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DNat n) (DNat n') = case decEq n n' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
dDecEq (DNat _) (DString _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DString _) (DReflectedKeyword _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DString _) (DNat _) =
  No $ \eq => case eq of Refl impossible
dDecEq (DString s) (DString s') = case decEq s s' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq Data where
  decEq = dDecEq

public export
Eq Data using decEqToEq where
  (==) = (==)

public export
Ord Data where
  DReflectedKeyword k < DReflectedKeyword k' = k < k'
  DReflectedKeyword _ < DNat _ = True
  DReflectedKeyword _ < DString _ = True
  DNat _ < DReflectedKeyword _ = False
  DNat n < DNat n' = n < n'
  DNat _ < DString _ = True
  DString _ < DReflectedKeyword _ = False
  DString _ < DNat _ = False
  DString s < DString s' = s < s'

public export
data ComputeAtom : Type where
  CAKeyword : Keyword -> ComputeAtom
  CAData : Data -> ComputeAtom

public export
Show ComputeAtom where
  show (CAKeyword k) = show k
  show (CAData d) = show d

public export
caShow : ComputeAtom -> String
caShow = show

public export
caDecEq : DecEqPred ComputeAtom
caDecEq (CAKeyword k) (CAKeyword k') = case decEq k k' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl
caDecEq (CAKeyword _) (CAData _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAData _) (CAKeyword _) =
  No $ \eq => case eq of Refl impossible
caDecEq (CAData d) (CAData d') = case decEq d d' of
  Yes Refl => Yes Refl
  No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq ComputeAtom where
  decEq = caDecEq

public export
Eq ComputeAtom using decEqToEq where
  (==) = (==)

public export
Ord ComputeAtom where
  CAKeyword k < CAKeyword k' = k < k'
  CAKeyword _ < CAData _ = True
  CAData _ < CAKeyword _ = False
  CAData d < CAData d' = d < d'

public export
CAFail : ComputeAtom
CAFail = CAKeyword Fail

public export
CAReflectedKeyword : Keyword -> ComputeAtom
CAReflectedKeyword = CAData . DReflectedKeyword

public export
CANat : Nat -> ComputeAtom
CANat = CAData . DNat

public export
CAString : String -> ComputeAtom
CAString = CAData . DString

public export
CExp : Type
CExp = SExp ComputeAtom

public export
CList : Type
CList = SList ComputeAtom

public export
Show CExp where
  show = fst (sexpShows show)

public export
Show CList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
csDecEq : DecEqPred CExp
csDecEq = sexpDecEq caDecEq

public export
cslDecEq : DecEqPred CList
cslDecEq = slistDecEq caDecEq

public export
DecEq CExp where
  decEq = csDecEq

public export
DecEq CList where
  decEq = cslDecEq

public export
Eq CExp using decEqToEq where
  (==) = (==)

public export
CSFail : CExp
CSFail = $^ CAFail
