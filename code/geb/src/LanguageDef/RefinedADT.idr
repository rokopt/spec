module LanguageDef.RefinedADT

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom

%default total

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Category of ranges of natural numbers with order-preserving maps ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

public export
record FinNERangeObj where
  constructor MkFinRange
  frStart : Nat
  frPredLength : Nat

public export
finNERangeLast : FinNERangeObj -> Nat
finNERangeLast (MkFinRange s pl) = pl + s

public export
finNERangeLength : FinNERangeObj -> Nat
finNERangeLength = S . frPredLength

public export
Show FinNERangeObj where
  show r =
    "[" ++ show (frStart r) ++ ".." ++ show (finNERangeLast r) ++ "](" ++
    show (finNERangeLength r) ++ ")"

public export
Eq FinNERangeObj where
  (==) (MkFinRange s1 pl1) (MkFinRange s2 pl2) =
    s1 == s2 && pl1 == pl2

public export
Ord FinNERangeObj where
  compare (MkFinRange s1 pl1) (MkFinRange s2 pl2) =
    case compare s1 s2 of
      EQ => compare pl1 pl2
      LT => LT
      GT => GT

public export
boundedBelow : Nat -> List Nat -> Type
boundedBelow min [] = ()
boundedBelow min (x :: xs) = (LTE min x, boundedBelow min xs)

public export
boundedAbove : Nat -> List Nat -> Type
boundedAbove max [] = ()
boundedAbove max (x :: xs) = (LTE x max, boundedAbove max xs)

public export
ordered : List Nat -> Type
ordered [] = ()
ordered [x] = ()
ordered (x :: x' :: xs) = (LTE x x', ordered (x' :: xs))

public export
boundedBelowSucc : {n : Nat} -> {l : List Nat} ->
  boundedBelow (S n) l -> boundedBelow n l
boundedBelowSucc {l=[]} _ = ()
boundedBelowSucc {l=(x :: xs)} (b, bs) = (lteSuccLeft b, boundedBelowSucc bs)

public export
record ListIsBoundedAndOrdered (predLen, start : Nat) (l : List Nat) where
  constructor BoundedOrderedListConditions
  validLength : length l = S predLen
  validLower : boundedBelow start l
  validUpper : boundedAbove (predLen + start) l
  validOrder : ordered l

public export
validIncList : (predLen : Nat) -> (start : Nat) ->
  (l : List Nat ** ListIsBoundedAndOrdered predLen start l)
validIncList Z s =
  ([s] **
   BoundedOrderedListConditions
    Refl
    (reflexive, ())
    (reflexive, ())
    ())
validIncList (S pl) s with (validIncList pl (S s))
  validIncList (S pl) s |
    (l ** BoundedOrderedListConditions validLen below above ord) =
      (s :: l **
       BoundedOrderedListConditions
        (cong S validLen)
        (reflexive, boundedBelowSucc below)
        (lteSuccRight $ lteAddLeft pl s,
         rewrite plusSuccRightSucc pl s in above)
        (case l of
          [] => ()
          x :: xs => (lteSuccLeft $ fst below, ord)))

public export
incList : (predLen : Nat) -> (start : Nat) -> List Nat
incList predLen start = fst $ validIncList predLen start

public export
incListLen :
  (predLen : Nat) -> (start : Nat) -> length (incList predLen start) = S predLen
incListLen predLen start = validLength $ snd $ validIncList predLen start

public export
incListBoundedBelow : (predLen : Nat) -> (start : Nat) ->
  boundedBelow start (incList predLen start)
incListBoundedBelow predLen start =
  validLower $ snd $ validIncList predLen start

public export
incListBoundedAbove : (predLen : Nat) -> (start : Nat) ->
  boundedAbove (predLen + start) (incList predLen start)
incListBoundedAbove predLen start =
  validUpper $ snd $ validIncList predLen start

public export
incListOrdered : (predLen : Nat) -> (start : Nat) ->
  ordered (incList predLen start)
incListOrdered predLen start =
  validOrder $ snd $ validIncList predLen start

public export
record FinNERangeMorph where
  constructor MkFinNERangeMorph
  frDomain : FinNERangeObj
  frCodomain : FinNERangeObj
  frMap : List Nat

public export
record FinNERangeMorphIsValid (morph : FinNERangeMorph) where
  constructor FinNERangeMorphConditions
  frValidLen : length morph.frMap = (finNERangeLength morph.frDomain)
  frBoundedBelow : boundedBelow (frStart morph.frCodomain) morph.frMap
  frBoundedAbove : boundedAbove (finNERangeLast morph.frCodomain) morph.frMap
  frOrdered : ordered morph.frMap

public export
ValidFinNERangeMorph : Type
ValidFinNERangeMorph = DPair FinNERangeMorph FinNERangeMorphIsValid

public export
Show FinNERangeMorph where
  show (MkFinNERangeMorph dom cod map) =
    "[" ++ show dom ++ "->" ++ show cod ++ ":" ++ show map ++ "]"

public export
Eq FinNERangeMorph where
  (==)
    (MkFinNERangeMorph dom1 cod1 map1)
    (MkFinNERangeMorph dom2 cod2 map2) =
      dom1 == dom2 && cod1 == cod2 && map1 == map2

public export
Ord FinNERangeMorph where
  compare
    (MkFinNERangeMorph dom1 cod1 map1)
    (MkFinNERangeMorph dom2 cod2 map2) =
      case compare dom1 dom2 of
        EQ => case compare cod1 cod2 of
          EQ => compare map1 map2
          LT => LT
          GT => GT
        LT => LT
        GT => GT

public export
finNERangeId : FinNERangeObj -> ValidFinNERangeMorph
finNERangeId r@(MkFinRange s pl) =
  (MkFinNERangeMorph r r (incList pl s) **
   (FinNERangeMorphConditions
    (incListLen pl s)
    (incListBoundedBelow pl s)
    (incListBoundedAbove pl s)
    (incListOrdered pl s)))

public export
Composable : FinNERangeMorph -> FinNERangeMorph -> Type
Composable g f = g.frDomain = f.frCodomain

public export
composeFinNERange :
  (g, f : ValidFinNERangeMorph) ->
  Composable g.fst f.fst ->
  (gf : ValidFinNERangeMorph **
   (gf.fst.frDomain = f.fst.frDomain,
    gf.fst.frCodomain = g.fst.frCodomain))
composeFinNERange g f c with (f.fst.frMap) proof pf
  composeFinNERange g f c | [] =
    let
      vl = f.snd.frValidLen
      vl' = replace {p=(\x => length x = finNERangeLength f.fst.frDomain)} pf vl
    in
    case vl' of Refl impossible
  composeFinNERange g f c | (i :: l) = ?composeFinNERange_hole

---------------------------------------------------
---------------------------------------------------
---- Simplex (augmented/algebraist's) category ----
---------------------------------------------------
---------------------------------------------------

----------------------------------
---- Simplex category objects ----
----------------------------------

-- The finite ordinal of the size equal to the natural number
-- that represents it.  We will treat it as an object of the
-- "augmented" or "algebraist's" version of the "simplex category",
-- known as `FinOrd`.  It is the category whose objects are finite ordinals
-- and whose morphisms are order-preserving maps.
--
-- Thus, 0 represents empty, and for all `n`, `S n` represents
-- [0..n] inclusive.
public export
FinOrdObj : Type
FinOrdObj = Nat

------------------------------------
---- Simplex category morphisms ----
------------------------------------

-- A representation of an order-preserving mapping from the ranges of natural
-- numbers [m..n] -> [m'..n'] (inclusive).
public export
data NatRangeMap : (m, n, m', n' : Nat) -> Type where
  NatRangeMapOne : (m, m', n', i : Nat) ->
    {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
    NatRangeMap m m m' n'
  NatRangeMapMulti : (m, n, m', n', i : Nat) ->
    {auto mltn : LT m n} ->
    {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
    NatRangeMap (S m) n i n' ->
    NatRangeMap m n m' n'

public export
natRangeToList : {0 m, n, m', n' : Nat} -> NatRangeMap m n m' n' -> List Nat
natRangeToList (NatRangeMapOne _ _ _ i) = [i]
natRangeToList (NatRangeMapMulti _ _ _ _ i rmap) = i :: natRangeToList rmap

public export
Show (NatRangeMap m n m' n') where
  show (NatRangeMapOne m m' n' i) =
    show m ++ "/" ++ show m ++ "->" ++ show i ++ "/" ++ show n'
  show (NatRangeMapMulti m n m' n' i rmap) =
    show m ++ "/" ++ show n ++ "->" ++ show i ++ "/" ++ show n' ++ ", " ++
    show rmap

public export
listToNatRange :
  (m, n, m', n' : Nat) -> Nat -> List Nat -> Maybe (NatRangeMap m n m' n')
listToNatRange m n m' n' i [] =
  case (decEq m n, isLTE m' i, isLTE i n') of
    (Yes Refl, Yes _, Yes _) => Just (NatRangeMapOne m m' n' i)
    (_, _) => Nothing
listToNatRange m n m' n' i (i' :: is) =
  case (isLT m n, isLTE m' i, isLTE i n', listToNatRange (S m) n i n' i' is) of
    (Yes _, Yes _, Yes _, Just rmap) => Just (NatRangeMapMulti m n m' n' i rmap)
    (_, _, _) => Nothing

public export
MkNatRange : (m, n, m', n', i : Nat) -> (l : List Nat) ->
  {auto valid : isJust (listToNatRange m n m' n' i l) = True} ->
  NatRangeMap m n m' n'
MkNatRange m n m' n' i l {valid} with (listToNatRange m n m' n' i l)
  MkNatRange m n m' n' i l {valid=Refl} | Just rng = rng
  MkNatRange m n m' n' i l {valid=Refl} | Nothing impossible

public export
natRangeLeftBounds : NatRangeMap m n m' n' -> LTE m n
natRangeLeftBounds (NatRangeMapOne _ _ _ _) = reflexive
natRangeLeftBounds (NatRangeMapMulti {mltn} _ _ _ _ _ _) = lteSuccLeft mltn

public export
natRangeRightBounds : NatRangeMap m n m' n' -> LTE m' n'
natRangeRightBounds (NatRangeMapOne {mlti} {iltn} _ _ _ _) =
  transitive mlti iltn
natRangeRightBounds (NatRangeMapMulti {mlti} {iltn} _ _ _ _ _ _) =
  transitive mlti iltn

public export
natRangeExtendCodomainBelow : NatRangeMap m n (S m') n' -> NatRangeMap m n m' n'
natRangeExtendCodomainBelow
  (NatRangeMapOne m (S m') n' i {mlti} {iltn}) =
    NatRangeMapOne
      m m' n' i
      {mlti=(lteSuccLeft mlti)}
      {iltn}
natRangeExtendCodomainBelow
  (NatRangeMapMulti m n (S m') n' i {mltn} {mlti} {iltn} nrm) =
    NatRangeMapMulti
      m n m' n' i nrm
      {mltn}
      {mlti=(lteSuccLeft mlti)}
      {iltn}

-- A diagonally-increasing mapping from [n..i+n] to [n..i+n].
public export
natRangeId : (n, i : Nat) -> NatRangeMap n (i + n) n (i + n)
natRangeId n 0 = NatRangeMapOne n n n n {mlti=reflexive} {iltn=reflexive}
natRangeId n (S i) =
  let ialn = lteAddLeft i n in
  NatRangeMapMulti
    n (S i + n) n (S i + n) n
    {mltn=(LTESucc ialn)}
    {mlti=reflexive}
    {iltn=(lteSuccRight ialn)}
    $
    rewrite plusSuccRightSucc i n in
    natRangeExtendCodomainBelow $ natRangeId (S n) i

public export
natRangeEval : {m, n, m', n' : Nat} -> NatRangeMap m n m' n' -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} -> Nat
natRangeEval (NatRangeMapOne _ _ _ i') _ = i'
natRangeEval {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i =
    case decEq m i of
      Yes Refl => i'
      No neq => natRangeEval rng i {mlti=(lteTolt mlti neq)} {iltn}

public export
natRangeEvalGT : {m, n, m', n' : Nat} ->
  (rng : NatRangeMap m n m' n') -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  LTE m' (natRangeEval rng i {mlti} {iltn})
natRangeEvalGT (NatRangeMapOne {mlti=mlti'} _ _ _ _) _ = mlti'
natRangeEvalGT {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
  with (decEq m i)
    natRangeEvalGT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} i n m' n' i' rng) i
      | Yes Refl = mlti'
    natRangeEvalGT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
      | No neq =
        transitive mlti' $ natRangeEvalGT rng i {mlti=(lteTolt mlti neq)}

public export
natRangeEvalLT : {m, n, m', n' : Nat} ->
  (rng : NatRangeMap m n m' n') -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  LTE (natRangeEval rng i {mlti} {iltn}) n'
natRangeEvalLT (NatRangeMapOne {iltn=iltn'} _ _ _ _) _ = iltn'
natRangeEvalLT {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
  with (decEq m i)
    natRangeEvalLT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} i n m' n' i' rng) i
      | Yes Refl = iltn'
    natRangeEvalLT {mlti} {iltn}
      (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} m n m' n' i' rng) i
      | No neq = natRangeEvalLT rng i {mlti=(lteTolt mlti neq)}

public export
natRangeEvalCert : {m, n, m', n' : Nat} ->
  (rng : NatRangeMap m n m' n') -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  (ev : Nat ** (LTE m' ev, LTE ev n'))
natRangeEvalCert rng i =
  (natRangeEval rng i ** (natRangeEvalGT rng i, natRangeEvalLT rng i))

public export
natRangeConstInc : (m, p, m', n', i : Nat) ->
  {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
  NatRangeMap m (p + m) m' n'
natRangeConstInc m 0 m' n' i {mlti} {iltn} =
  NatRangeMapOne m m' n' i
natRangeConstInc m (S p) m' n' i {mlti} {iltn} =
  NatRangeMapMulti m (S p + m) m' n' i
  {mltn=(LTESucc $ lteAddLeft p m)}
  {mlti}
  {iltn}
  $
  rewrite plusSuccRightSucc p m in
  natRangeConstInc (S m) p i n' i {mlti=reflexive}

public export
natRangeConst : (m, n, m', n', i : Nat) ->
  {auto mltn : LTE m n} ->
  {auto mlti : LTE m' i} -> {auto iltn : LTE i n'} ->
  NatRangeMap m n m' n'
natRangeConst m n m' n' i {mltn} {mlti} {iltn} =
  rewrite sym (plusMinusLte m n mltn) in
  natRangeConstInc m (minus n m) m' n' i

public export
natRangeSlice : {m, n, m', n' : Nat} -> NatRangeMap m n m' n' -> (i : Nat) ->
  {auto mlti : LTE m i} -> {auto iltn : LTE i n} ->
  (i' : Nat ** (LTE m' i', LTE i' n', NatRangeMap i n i' n'))
natRangeSlice {mlti} {iltn}
  (NatRangeMapOne {mlti=mlti'} {iltn=iltn'} _ _ _ i') i =
    (i' **
     (mlti', iltn',
      natRangeConst i n i' n' i' {mltn=(iltn)} {iltn=(iltn')} {mlti=reflexive}))
natRangeSlice {mlti} {iltn}
  (NatRangeMapMulti {mlti=mlti'} {iltn=iltn'} {mltn=mltn'} m n m' n' i' rng) i =
    case decEq m i of
      Yes Refl =>
        (i' **
         (mlti', iltn',
          NatRangeMapMulti
            {mlti=reflexive} {iltn=iltn'} {mltn=mltn'}
            m n i' n' i' rng))
      No neq =>
        let
          (i'' ** (ltmi'', ltin'', rng'')) =
            natRangeSlice rng i {mlti=(lteTolt mlti neq)} {iltn}
        in
        (i'' ** (transitive mlti' ltmi'', ltin'', rng''))

-- Compose a mapping from [m'..n'] to [m''..n''] after a mapping from
-- [m..n] to [m'..n'] to produce a mapping from [m..n] to [m''..n''].
public export
natRangeCompose : {m, n, m', n', m'', n'' : Nat} ->
  NatRangeMap m' n' m'' n'' -> NatRangeMap m n m' n' -> NatRangeMap m n m'' n''
natRangeCompose {m} {n} {m'} {n'} {m''} {n''} rng' rng =
  case rng of
    NatRangeMapOne p q r i {mlti} {iltn} =>
      let (ev' ** (evgt', evlt')) = natRangeEvalCert rng' i {mlti} {iltn} in
      NatRangeMapOne p m'' n'' ev' {mlti=evgt'} {iltn=evlt'}
    NatRangeMapMulti {mltn} {mlti} {iltn} p q r s j rngint =>
      let
        (i'' ** (ltmi'', ltin'', rng'')) = natRangeSlice rng' j
      in
      NatRangeMapMulti
        p q m'' n'' i''
        {mltn}
        {mlti=ltmi''}
        {iltn=ltin''}
        $
        natRangeCompose rng'' rngint

-- A morphism in the augmented simplex category, namely, an
-- order-preserving map.
public export
data FinOrdMorph : FinOrdObj -> FinOrdObj -> Type where
  FinOrdFromVoid : (n : Nat) -> FinOrdMorph 0 n
  FinOrdRange : NatRangeMap 0 n 0 n' -> FinOrdMorph (S n) (S n')

public export
finOrdMorphToList : {0 m, n : Nat} -> FinOrdMorph m n -> List Nat
finOrdMorphToList (FinOrdFromVoid _) = []
finOrdMorphToList (FinOrdRange rmap) = natRangeToList rmap

public export
Show (FinOrdMorph m n) where
  show (FinOrdFromVoid 0) = "([]->[])"
  show (FinOrdFromVoid (S n)) = "([]->[0.." ++ show n ++ "])"
  show (FinOrdRange rmap) = "(" ++ show rmap ++ ")"

public export
listToFinOrdMorph : (m, n : Nat) -> List Nat -> Maybe (FinOrdMorph m n)
listToFinOrdMorph 0 n [] = Just $ FinOrdFromVoid n
listToFinOrdMorph 0 _ (_ :: _) = Nothing
listToFinOrdMorph _ 0 (_ :: _) = Nothing
listToFinOrdMorph (S _) _ [] = Nothing
listToFinOrdMorph _ (S _) [] = Nothing
listToFinOrdMorph (S n) (S n') (i :: l) = case listToNatRange 0 n 0 n' i l of
  Just rmap => Just (FinOrdRange rmap)
  Nothing => Nothing

public export
MkFinOrdMorph : (m, n : Nat) -> (l : List Nat) ->
  {auto valid : isJust (listToFinOrdMorph m n l) = True} -> FinOrdMorph m n
MkFinOrdMorph m n l {valid} with (listToFinOrdMorph m n l)
  MkFinOrdMorph m n l {valid=Refl} | Just morph = morph
  MkFinOrdMorph m n l {valid=Refl} | Nothing impossible

public export
finOrdId : (n : Nat) -> FinOrdMorph n n
finOrdId 0 = FinOrdFromVoid 0
finOrdId (S n) =
  FinOrdRange $ rewrite sym (plusZeroRightNeutral n) in natRangeId 0 n

public export
finOrdCompose : {m, n, p : Nat} ->
  FinOrdMorph n p -> FinOrdMorph m n -> FinOrdMorph m p
finOrdCompose {m=0} {n} {p} _ (FinOrdFromVoid n) = FinOrdFromVoid p
finOrdCompose {m=(S m)} {n=0} (FinOrdFromVoid _) _ impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=0} _ _ impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=(S p)} (FinOrdFromVoid _) _ impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=(S p)} _ (FinOrdFromVoid _) impossible
finOrdCompose {m=(S m)} {n=(S n)} {p=(S p)}
  (FinOrdRange np) (FinOrdRange mn) = FinOrdRange $ natRangeCompose np mn

---------------------
---------------------
---- Finite ADTs ----
---------------------
---------------------

public export
data FinADTObj : Type where
  FinADTOrd : FinADTObj
  FinProduct : List FinADTObj -> FinADTObj
  FinCoproduct : List FinADTObj -> FinADTObj

mutual
  public export
  interpFinADTObj : FinADTObj -> Type
  interpFinADTObj FinADTOrd = FinOrdObj
  interpFinADTObj (FinProduct l) = interpFinProduct l
  interpFinADTObj (FinCoproduct l) = interpFinCoproduct l

  public export
  interpFinNEProduct : FinADTObj -> List FinADTObj -> Type
  interpFinNEProduct t [] =
    interpFinADTObj t
  interpFinNEProduct t (t' :: ts) =
    Pair (interpFinADTObj t) $ interpFinNEProduct t' ts

  public export
  interpFinProduct : List FinADTObj -> Type
  interpFinProduct [] = Unit
  interpFinProduct (t :: ts) = interpFinNEProduct t ts

  public export
  interpFinCoproduct : List FinADTObj -> Type
  interpFinCoproduct [] = Void
  interpFinCoproduct (t :: ts) = interpFinNECoproduct t ts

  public export
  interpFinNECoproduct : FinADTObj -> List FinADTObj -> Type
  interpFinNECoproduct t [] =
    interpFinADTObj t
  interpFinNECoproduct t (t' :: ts) =
    Either (interpFinADTObj t) $ interpFinNECoproduct t' ts

public export
data FinADTMorph : FinADTObj -> FinADTObj -> Type where

public export
data FinADTFunctor : Type where
  FinIdF : FinADTFunctor
  FinComposeF : FinADTFunctor -> FinADTFunctor -> FinADTFunctor
  FinProductF : List FinADTFunctor -> FinADTFunctor
  FinCoproductF : List FinADTFunctor -> FinADTFunctor

-------------------------------------
-------------------------------------
---- S-expressions made of pairs ----
-------------------------------------
-------------------------------------

public export
SExpBaseF : Type -> Type
SExpBaseF = ProductMonad

public export
SExpAlg : Type -> Type
SExpAlg = Algebra SExpBaseF

public export
SExpCoalg : Type -> Type
SExpCoalg = Coalgebra SExpBaseF

public export
SExpTermF : Type -> Type -> Type
SExpTermF = TermFunctor SExpBaseF

public export
SExpTreeF : Type -> Type -> Type
SExpTreeF = TreeFunctor SExpBaseF

public export
SExpTermAlg : Type -> Type -> Type
SExpTermAlg = TermAlgebra SExpBaseF

public export
SExpTreeCoalg : Type -> Type -> Type
SExpTreeCoalg = TreeCoalgebra SExpBaseF

public export
FreeSExp : Type -> Type
FreeSExp = FreeMonad SExpBaseF

public export
CofreeSExp : Type -> Type
CofreeSExp = CofreeComonad SExpBaseF

public export
SPairF : Type -> Type -> Type
SPairF var carrier = ProductMonad (SExpTermF var carrier)

public export
SPairTermF : Type -> Type -> Type
SPairTermF var = TermFunctor (ProductMonad . SExpTermF var) var

public export
SPairTreeF : Type -> Type -> Type
SPairTreeF var = TreeFunctor (ProductMonad . SExpTermF var) var

---------------------
---------------------
---- Finite ADTs ----
---------------------
---------------------

public export
data ADTObjF : Type -> Type where
  ADTF : TupleP (TupleP carrier) -> ADTObjF carrier

public export
ADTObjAlgebra : Type -> Type
ADTObjAlgebra = Algebra ADTObjF

public export
ADTObjCoalgebra : Type -> Type
ADTObjCoalgebra = Coalgebra ADTObjF

public export
FreeADTObj : Type -> Type
FreeADTObj = FreeMonad ADTObjF

public export
CofreeADTObj : Type -> Type
CofreeADTObj = CofreeComonad ADTObjF

public export
MuADTObj : Type
MuADTObj = Mu ADTObjF

public export
NuADTObj : Type
NuADTObj = Nu ADTObjF

public export
adtCases : {carrier : Type} -> ADTObjF carrier -> TupleP (TupleP carrier)
adtCases (ADTF t) = t

public export
adtIndex : {carrier : Type} -> ADTObjF carrier -> Type
adtIndex = TupleIndex . adtCases

public export
adtConstructor :
  {carrier : Type} -> (adt : ADTObjF carrier) -> adtIndex adt -> TupleP carrier
adtConstructor adt i = TupleElem (adtCases adt) i

public export
adtCase :
  {carrier : Type} -> (adt : ADTObjF carrier) -> adtIndex adt -> TupleP carrier

public export
record ADTMorphCarrier (objCarrier : Type) where
  constructor MkADTMorphCarrier
  morphObj : Type
  morphSignature : morphObj -> (TupleP objCarrier, objCarrier)

-- Given a `carrier` tuple constant types in a product category, `ADTObjF`
-- is a polynomial ADT comprising coproducts of products of types drawn
-- from the tuple of input (carrier) types.
public export
data ADTObjProjF : TupleP Type -> Type where
  ADT : {carrier : TupleP Type} ->
    TupleP (TupleP (TupleIndex {atom=Type} carrier)) -> ADTObjProjF carrier

public export
ADTProductObjF : TupleP Type -> TupleP Type
ADTProductObjF t = mapTupleP (const $ ADTObjProjF t) t

public export
LengthEquals : (carrier : Type) -> (Nat, List carrier) -> Type
LengthEquals _ (n, l) = n = length l

-- A list paired with its length (effectively, storing its length together
-- with the list at "runtime").
public export
ListN : Type -> Type
ListN carrier = (nl : (Nat, List carrier) ** LengthEquals carrier nl)

-- A finite-dimensional "matrix" with variable numbers of elements per row.
-- The parameter is the dimension minus one.
public export
VarMatrixD : (predDimension : Nat) -> Type -> Type
VarMatrixD Z carrier = ListN carrier
VarMatrixD (S n) carrier = ListN (VarMatrixD n carrier)

-- A finite-dimensional matrix of natural numbers.
-- The parameter is the dimension minus one.
VarMatrixN : (predDimension : Nat) -> Type
VarMatrixN = flip VarMatrixD Nat

public export
record FiniteShape where
  constructor MkFiniteShape
  numObjects : Nat
  numMorphisms : Nat
  domains : Vect numMorphisms (Fin numObjects)
  codomains : Vect numMorphisms (Fin numObjects)

-------------------------------
-------------------------------
---- Refined S-expressions ----
-------------------------------
-------------------------------

-- We define a category inductively through applications of the
-- following type constructors:
--
--  - `Atom` (for some given metalanguage atom type, which must be isomorphic
--  -         to the natural numbers or some subset of them, which in particular
--  -         means that they have a decidable equality)
--  - `Nat`
--  - `RefinedList` (indexed by number of atoms in the list)
--  - `RefinedSexp` (indexed by total number of atoms in the expression)
--
-- We define the category by treating the type constructors as
-- monads and comonads, and the function definitions as natural
-- transformations, which in turn are derived from compositions of
-- the units and counits of adjunctions.

public export
record RefinedSexpCarrier where
  constructor MkRefinedSexpCarrier
  RefinedSexpFunctorCarrier : Type
  RefinedSexpNatTransCarrier : Type
  RefinedSexpNatTransSignatureCarrier :
    RefinedSexpNatTransCarrier ->
    (RefinedSexpFunctorCarrier, RefinedSexpFunctorCarrier)

public export
data RefinedSexpFunctorF : (atom : Type) -> RefinedSexpCarrier -> Type where

public export
data RefinedSexpNatTransF : (atom : Type) -> RefinedSexpCarrier -> Type where

public export
RefinedSexpNatTransSignatureF : {atom : Type} ->
  (carrier : RefinedSexpCarrier) ->
  RefinedSexpNatTransF atom carrier ->
  (RefinedSexpNatTransF atom carrier, RefinedSexpNatTransF atom carrier)
RefinedSexpNatTransSignatureF {atom} carrier newNatTrans impossible

mutual
  public export
  data RefinedSexpFunctor : (atom : Type) -> Type where
    InRSF :
      RefinedSexpFunctorF atom (RefinedSexpData atom) ->
      RefinedSexpFunctor atom

  public export
  data RefinedSexpNatTrans : (atom : Type) -> Type where
    InRSNT :
      RefinedSexpNatTransF atom (RefinedSexpData atom) ->
      RefinedSexpNatTrans atom

  public export
  RefinedSexpNatTransSignature : {atom : Type} ->
    RefinedSexpNatTrans atom ->
    (RefinedSexpFunctor atom, RefinedSexpFunctor atom)
  RefinedSexpNatTransSignature (InRSNT _) impossible

  public export
  RefinedSexpData : (atom : Type) -> RefinedSexpCarrier
  RefinedSexpData atom =
    MkRefinedSexpCarrier
      (RefinedSexpFunctor atom)
      (RefinedSexpNatTrans atom)
      (RefinedSexpNatTransSignature {atom})

--------------------
--------------------
---- Core types ----
--------------------
--------------------

-----------------------
---- S-expressions ----
-----------------------

public export
data SexpClass : Type where
  SEXP : SexpClass
  SLIST : SexpClass

public export
SexpObject : Type
SexpObject = ProductCatObject SexpClass

public export
SexpObjectMap : Type
SexpObjectMap = ProductCatObjectEndoMap SexpClass

public export
data SexpFunctor :
    (atom : Type) -> (carrier : SexpObject) -> SexpObject where
  SexpF :
    atom -> carrier SLIST -> SexpFunctor atom carrier SEXP
  SlistF :
    ListF (carrier SEXP) (carrier SLIST) ->
    SexpFunctor atom carrier SLIST

public export
SexpAlg : Type -> SexpObject -> Type
SexpAlg = ProductCatAlgebra {idx=SexpClass} . SexpFunctor

public export
FreeSexp : Type -> SexpObject -> SexpObject
FreeSexp atom = ProductCatFreeMonad {idx=SexpClass} (SexpFunctor atom)

public export
MuSexp : Type -> SexpObject
MuSexp atom = MuProduct {idx=SexpClass} (SexpFunctor atom)

public export
Sexp : Type -> Type
Sexp = flip MuSexp SEXP

public export
Slist : Type -> Type
Slist = flip MuSexp SLIST

public export
SexpCoalg : Type -> SexpObject -> Type
SexpCoalg = ProductCatCoalgebra {idx=SexpClass} . SexpFunctor

public export
CofreeSexp : Type -> SexpObject -> SexpObject
CofreeSexp atom = ProductCatCofreeComonad {idx=SexpClass} (SexpFunctor atom)

public export
NuSexp : Type -> SexpObject
NuSexp atom = NuProduct {idx=SexpClass} (SexpFunctor atom)

-------------------------------------------------
-------------------------------------------------
---- The category of polynomial endofunctors ----
-------------------------------------------------
-------------------------------------------------

public export
record FinNatPoly where
  constructor MkFinNatPoly
  numTerms : Nat
  coefficients : LList Nat numTerms
  trimmed : Not (head' (llList coefficients) = Just 0)

public export
Show FinNatPoly where
  show (MkFinNatPoly _ c _) = show c

public export
InitFinNatPoly :
  (l : List Nat) -> {auto ok : (head' l /= Just 0) = True} -> FinNatPoly
InitFinNatPoly l {ok} = MkFinNatPoly (length l) (InitLList l) $
  \isz =>
    case replace {p=(\hl => (hl /= Just 0) = True)} isz ok of Refl impossible

public export
interpretFinNatPoly : FinNatPoly -> Nat -> Nat
interpretFinNatPoly (MkFinNatPoly d cs _) n =
  llCata (MkLLAlg Z (\i, c, acc => acc + c * (power n i))) cs

public export
record MultiVarTerm (constant, variable : Type) where
  PolyTerm : (constant, variable)

public export
mvConst : MultiVarTerm constant variable -> constant
mvConst = fst . PolyTerm

public export
mvVar : MultiVarTerm constant variable -> variable
mvVar = snd . PolyTerm

public export
record MultiVarPoly (constant, variable : Type) where
  PolyTerms : List (MultiVarTerm constant variable)

public export
numTerms : MultiVarPoly constant variable -> Nat
numTerms = length . PolyTerms

public export
mvNth :
  (mvp : MultiVarPoly constant variable) -> (n : Nat) ->
  {auto ok : InBounds n (PolyTerms mvp)} ->
  MultiVarTerm constant variable
mvNth mvp n = index n (PolyTerms mvp)

---------------
---------------
---- Paths ----
---------------
---------------

public export
EdgeProjectionType : Type -> Type -> Type
EdgeProjectionType vertex edge = edge -> (vertex, vertex)

public export
record PathCarrier (vertex : Type) where
  constructor EdgeFibration
  EdgeTotal : Type
  EdgeProjection : EdgeProjectionType vertex EdgeTotal

public export
edgeSource : {carrier : PathCarrier vertex} -> EdgeTotal carrier -> vertex
edgeSource {carrier} = fst . EdgeProjection carrier

public export
edgeTarget : {carrier : PathCarrier vertex} -> EdgeTotal carrier -> vertex
edgeTarget {carrier} = snd . EdgeProjection carrier

public export
data PathTotalF :
    (vEq : vertex -> vertex -> Type) -> PathCarrier vertex -> Type where
  LoopF :
    {carrier : PathCarrier vertex} ->
    vertex ->
    PathTotalF vEq carrier
  ConcatF :
    {carrier : PathCarrier vertex} ->
    (tail, head : EdgeTotal carrier) ->
    {auto valid :
      vEq (edgeSource {carrier} tail) (edgeTarget {carrier} head)} ->
    PathTotalF vEq carrier

public export
PathDomainF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  PathTotalF vEq carrier ->
  vertex
PathDomainF carrier (LoopF v) = v
PathDomainF carrier (ConcatF tail head) = edgeSource {carrier} head

public export
PathCodomainF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  PathTotalF vEq carrier ->
  vertex
PathCodomainF carrier (LoopF v) = v
PathCodomainF carrier (ConcatF tail head) = edgeTarget {carrier} tail

public export
PathProjectionF :
  {vertex : Type} ->
  {vEq : vertex -> vertex -> Type} ->
  (carrier : PathCarrier vertex) ->
  EdgeProjectionType vertex (PathTotalF vEq carrier)
PathProjectionF carrier edge =
  (PathDomainF carrier edge, PathCodomainF carrier edge)

public export
PathF : {vertex : Type} ->
  (vertex -> vertex -> Type) ->
  PathCarrier vertex ->
  PathCarrier vertex
PathF vEq carrier =
  EdgeFibration (PathTotalF vEq carrier) (PathProjectionF {vEq} carrier)

----------------------------
----------------------------
---- Geb terms in Idris ----
----------------------------
----------------------------

-- Geb itself is a pure specification.  `GebTerm` is an Idris type whose
-- terms represent various concepts of Geb.  Because a term of `GebTerm`
-- might represent any of several different concepts, the type is indexed
-- by a type of atoms which classify which concept a given term represents.
-- This makes `GebTerm` a type family; it's effectively simulating a
-- definition by a large mutual recursion, but using an index intead of many
-- different Idris types allows us to interpret Geb in Idris by interpreting
-- just that one type.  I find it less confusing and more convenient than a big
-- mutual recursion.

-------------------------
---- Term definition ----
-------------------------

-- We define `GebTerm` -- an Idris type -- as a fixed point of a
-- polynomial endofunctor of Idris, in the same style in which we will define
-- types of Geb itself.  In particular, that will allow us to write a homoiconic
-- representation of `GebTerm` _as_ a term of `GebTerm` in a way
-- which parallels the Idris definition of `GebTerm`.
--
-- Because `GebTerm`, as described above, represents a number of different
-- concepts, we can view it as an object in a finite product category, where
-- each concept -- which we call a "class" in the context of defining
-- `GebTerm` -- is one of the categories.
--
-- So we first define `GebTermF`, a (polynomial) endofunctor in the product
-- category of all the classes.  Having defined that functor, we'll take a
-- fixed point of it (which we will be able to do because it is polynomial),
-- and then we'll have a `GebTerm` which comprises the Idris
-- representation of terms of Geb.
--
-- Below is the product category in which `GebTerm` lives; therefore it's
-- the category on which we will build an endofunctor, `GebTermF`, from
-- which we will derive `GebTerm` as a fixpoint (initial algebra).
--
-- We represent the product category as a function from a finite
-- index type rather than as, say, nested pairs or a list -- those are all
-- isomorphic, but I feel that the function representation produces the most
-- readable code.
--
-- The aspects of the product category that we define are its objects, its
-- morphisms, and its endofunctors.

public export
GebTermProductCatObject : Type
GebTermProductCatObject = ProductCatObject GebAtom

-- A morphism in a product category is a product of morphisms.
-- (In an Idris category, morphisms are functions.)
public export
GebTermProductCatMorphism :
  GebTermProductCatObject -> GebTermProductCatObject -> Type
GebTermProductCatMorphism = ProductCatMorphism {idx=GebAtom}

-- An endofunctor on the Idris product category in which Geb terms are defined
-- is a function on objects of the product category together with a function
-- on morphisms that respects it.

public export
GebTermProductCatObjectMap : Type
GebTermProductCatObjectMap = ProductCatObjectEndoMap GebAtom

public export
GebTermProductCatMorphismMap : GebTermProductCatObjectMap -> Type
GebTermProductCatMorphismMap = ProductCatMorphismEndoMap

public export
GebTermProductCatEndofunctor : Type
GebTermProductCatEndofunctor = ProductCatEndofunctor GebAtom

------------------------------------------
---- Term-checking and interpretation ----
------------------------------------------


---------------------------------
---------------------------------
---- Metalanguage fibrations ----
---------------------------------
---------------------------------

-----------------------------
-----------------------------
---- Metalanguage arrows ----
-----------------------------
-----------------------------

-- We refer to a pair of a pair of vertices in a directed graph and an edge
-- from the first vertex in the pair to the second vertex in the pair as an
-- "arrow".

----------------------------
----------------------------
---- Generalized arrows ----
----------------------------
----------------------------

-- We refer to a pair of a pair of vertices in a directed graph and an edge
-- from the first vertex in the pair to the second vertex in the pair as an
-- "arrow".

{-
public export
ArrowSig : Type -> Type
ArrowSig vertexType = (vertexType, vertexType)

public export
EdgeType : Type -> Type
EdgeType vertexType = ArrowSig vertexType -> Type

public export
Arrow : {vertexType : Type} -> EdgeType vertexType -> Type
Arrow {vertexType} arrowType = DPair (ArrowSig vertexType) arrowType

public export
arrowSig : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> ArrowSig vertexType
arrowSig (sig ** _) = sig

public export
arrowEdge : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  (arrow : Arrow arrowType) -> arrowType (arrowSig arrow)
arrowEdge (_ ** edge) = edge

public export
arrowSource : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> vertexType
arrowSource = fst . arrowSig

public export
arrowTarget : {vertexType : Type} -> {arrowType : EdgeType vertexType} ->
  Arrow arrowType -> vertexType
arrowTarget = snd . arrowSig
-}

----------------------------------------
----------------------------------------
---- Equivalence and term rewriting ----
----------------------------------------
----------------------------------------

------------------------------------
---- Free equivalence relations ----
------------------------------------

-- A type which represents witnesses to an equivalence relation.
-- A term of this type may be used as a rewrite rule.

public export
data FreeEquivF : Type -> Type -> Type where
  -- `EqRefl` represents the equivalence between some term `x` of type `a`
  -- and itself.  The reason it has _two_ parameters of type `a` is that
  -- a free generator of witnesses to an equivalence relation is in effect,
  -- and will be used as, a rewrite rule.  Asserting `EqRefl` between `x`
  -- and `y` is a claim that there is a _decidable_ equality between the two
  -- which can be decided when the term is validated (typechecked).
  EqRefl : a -> a -> FreeEquivF a carrier
  -- Given a term of `carrier`, which represents an equivalence bewteen
  -- terms `x` and `y` of `a`, `EqSym` represents an equivalence between
  -- `y` and `x`.
  EqSym : a -> a -> carrier -> FreeEquivF a carrier
  -- Given terms `eq` and `eq'` of type `carrier`, which respectively
  -- represent the equivalences of `x` and `y` and of `y` and `z` of type `a`,
  -- `EqTrans` represents the equivalence of `x` and `z`.
  EqTrans : a -> a -> a -> carrier -> carrier -> FreeEquivF a carrier

public export
Bifunctor FreeEquivF where
  bimap f _ (EqRefl x y) = EqRefl (f x) (f y)
  bimap f g (EqSym x y eq) = EqSym (f x) (f y) $ g eq
  bimap f g (EqTrans x y z eq eq') = EqTrans (f x) (f y) (f z) (g eq) (g eq')

-- Tests for the validity of a witness to an equivalence relation,
-- and if it is valid, returns which terms are being witnessed to be equivalent.
public export
checkFreeEquiv :
  Eq a =>
  ((a, a) -> Maybe (a, a)) ->
  FreeEquivF a (a, a) -> Maybe (a, a)
checkFreeEquiv eqa (EqRefl x y) =
  case eqa (x, y) of
    Just (x', y') => if x == x' && y == y' then Just (x, y) else Nothing
    Nothing => Nothing
checkFreeEquiv eqa (EqSym x y eq) =
  case eqa eq of
    Just (x', y') => if x == x' && y == y' then Just (y, x) else Nothing
    Nothing => Nothing
checkFreeEquiv eqa (EqTrans x y z eq eq') =
  case (eqa eq, eqa eq') of
    (Just (x', y'), Just (y'', z')) =>
      if x == x' && y == y' && y' == y'' && z == z' then
        Just (x, z)
      else
        Nothing
    (Nothing, _) => Nothing
    (_, Nothing) => Nothing

--------------------------
---- Rewritable terms ----
--------------------------

-- A rewritable term type is a term type accompanied with a (free) equivalence
-- relation, a witness to which may be used _as_ a term.
public export
data RewritableTermF : Type -> Type where
  Rewrite : FreeEquivF carrier carrier -> RewritableTermF carrier

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

-- When freely generating categories, we are producing _three_ types:
--
--  - Objects
--  - Morphisms
--  - Equalities
--
-- The equalities come from the identity and associativity laws.  When we
-- define categories in the usual way by proving that existing constructs
-- satisfy the axioms, we must supply proofs of those equalities.  But when
-- we freely generate a category, we must freely generate those equalities
-- to _make_ the generated category satisfy the axioms.
--
-- Consequently, throughout the rest of the development of expressions, the
-- algebras which typecheck objects and morphisms will _not_ use metalanguage
-- equalities -- they will use (and update) carrier types representing
-- free equivalence relations (see `FreeEquivF` above).  This must include
-- the expressions representing objects and morphisms -- our free generation
-- may produce some objects indirectly via morphisms, and since morphisms
-- may exhibit free equalities, objects may as well, unlike in traditional
-- category theory.  The typechecking of morphisms must respect a carrier
-- free equivalence on _objects_, because an equivalence of objects may allow a
-- composition which would not have been allowed by intensional equality
-- (meaning that the domain of the following morphism was not intensionally
-- equal to the codomain of the preceding morphism).
public export
data MorphismF : Type -> Type -> Type where
  -- An identity morphism is labeled by the object which is its
  -- domain and codomain.
  IdentityF :
    object -> MorphismF object carrier
  -- A composition is labeled by its source, intermediate object, and
  -- target, followed by the two morphisms being composed, with the
  -- following morphism listed first, as in usual mathematical notation.
  ComposeF :
    object -> object -> object -> carrier -> carrier -> MorphismF object carrier

public export
checkMorphism :
  (Eq object, Eq carrier) =>
  (object -> Maybe object) ->
  (carrier -> Maybe (object, object)) ->
  (MorphismF object carrier -> Maybe (object, object))
checkMorphism checkObj checkMorph (IdentityF obj) =
  case checkObj obj of
    Just obj' => Just (obj', obj')
    Nothing => Nothing
checkMorphism checkObj checkMorph (ComposeF a b c g f) =
  case (checkObj a, checkObj b, checkObj c, checkMorph g, checkMorph f) of
    (Just a', Just b', Just c', Just (domg, codg), Just (domf, codf)) =>
      if a' == domf && b' == codf && b' == domg && c' == codg then
        Just (a', c')
      else
        Nothing
    _ => Nothing

public export
Bifunctor MorphismF where
  bimap f _ (IdentityF v) = IdentityF $ f v
  bimap f g (ComposeF s i t q p) = ComposeF (f s) (f i) (f t) (g q) (g p)

-- Free categories produce a free equivalence on morphisms, correpsonding to
-- the identity and associativity laws.
public export
data MorphismEqF : Type -> Type where
  -- Rewrite the morphism `(id . f)` to `f`.
  RewriteIDLeft : morphism -> MorphismEqF morphism
  -- Rewrite the morphism `(f . id)` to `f`.
  RewriteIDRight : morphism -> MorphismEqF morphism
  -- Rewrite the morphism `(f . g) . h` to `f . (g . h)`.
  RewriteAssoc : morphism -> morphism -> morphism -> MorphismEqF morphism

-- Generate the free equivalence relation from the identity and associativity
-- laws.
public export
CoequalizedMorphismF : Type -> Type
CoequalizedMorphismF carrier = FreeEquivF (MorphismEqF carrier) carrier

-- Generate the refined type of morphisms quotiented by the rewrite rules
-- (which are the axioms of category theory).
public export
data RefinedMorphismF : Type -> Type -> Type where
  RawMorphism :
    MorphismF object carrier -> RefinedMorphismF object carrier
  CoequalizedMorphism :
    CoequalizedMorphismF (RefinedMorphismF object carrier) ->
    RefinedMorphismF object carrier

----------------------------------
----------------------------------
---- Term-building categories ----
----------------------------------
----------------------------------

-- These are the categories we need in order to define the objects
-- and morphisms of the refined first-order ADT category -- the smallest one
-- in which there is an object which we can interpret in Idris as
-- `RefinedADTCat`.

-- Generate objects for a category which can support at least
-- substitution:  initial and terminal objects, and products and coproducts.
public export
data SubstCatObjF : Type -> Type where
  SubstInitial : SubstCatObjF carrier
  SubstTerminal : SubstCatObjF carrier
  SubstProduct : carrier -> carrier -> SubstCatObjF carrier
  SubstCoproduct : carrier -> carrier -> SubstCatObjF carrier

-- Generate morphisms for a category which can support at least substitution.
public export
data SubstCatMorphismF : Type -> Type -> Type where
  -- The left adjoint of the unique functor from the substitution category
  -- to the terminal category (which is the discrete one-object category).
  SubstFromInitial : object -> SubstCatMorphismF object carrier

  -- The right adjoint of the unique functor from the substitution category
  -- to the terminal category.
  SubstToTerminal : object -> SubstCatMorphismF object carrier

  -- The right adjoint of the diagonal functor (the diagonal functor goes
  -- from the substitution category to the product category, so its adjoints
  -- go from the product category to the substitution category).
  SubstProductIntro : (dom, cod, cod' : object) ->
    carrier -> carrier -> SubstCatMorphismF object carrier

  -- The left projection of the counit of the product adjunction
  -- (which is a morphism in the substitution category).
  SubstProductElimLeft : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  -- The right projection of the counit of the product adjunction.
  SubstProductElimRight : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductIntroLeft : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductIntroRight : (dom, cod : object) ->
    carrier -> SubstCatMorphismF object carrier

  SubstCoproductElim : (dom, dom', cod : object) ->
    carrier -> carrier -> SubstCatMorphismF object carrier

public export
data RefinedSubstObjF : Type -> Type -> Type where
  SubstEqualizer : object -> object -> morphism -> morphism ->
    RefinedSubstObjF object morphism

  SubstCoequalizer : object -> object -> morphism -> morphism ->
    RefinedSubstObjF object morphism

public export
data RefinedSubstMorphismF : Type -> Type -> Type where

public export
SubstCatObjFree : Type -> Type
SubstCatObjFree = FreeMonad SubstCatObjF

public export
SubstCatObj : Type
SubstCatObj = Mu SubstCatObjF

-----------------------------------------------------------
-----------------------------------------------------------
---- Substitution category in the metalanguage (Idris) ----
-----------------------------------------------------------
-----------------------------------------------------------

-- public export
-- data MetaSubstCatObjAlg : Type -> Type) where

----------------------------------
----------------------------------
----- Polynomial endofunctors ----
----------------------------------
----------------------------------

-- Expressions are drawn from four categories determined by the presence
-- or absence of each of the following pairs of universal properties:
--
--  - Equalizers & coequalizers
--    (Categories with them are called "refined"; those without are "unrefined")
--  - Initial algebras & terminal coalgebras
--    (Categories with them are "first-order"; those without are "zeroth-order")
--
-- The zeroth-order categories may also be called "substitution" categories.
--
-- All four categories have each of the following pairs of universal properties:
--
--  - Initial objects & terminal objects
--  - Products & coproducts
--
-- All the types until the end of the `Expression` section are zeroth-order,
-- even though they _have_ initial algebras and terminal coalgebras, because
-- they are all defined in the style of "datatypes à la carte" -- in effect,
-- this means that we are programming in the category of polynomial functors
-- of the zeroth-order categories.  At the end of the `Expression` section,
-- we generate the full forms of expressions by taking the fixpoints and
-- cofixpoints of the datatypes previously defined; those types live only in
-- the first-order categories.

----------------------------------
----------------------------------
----- Polynomial endofunctors ----
----------------------------------
----------------------------------

public export
data PolynomialFunctorF : Type -> Type -> Type where
  -- See https://ncatlab.org/nlab/show/polynomial+functor#definition :
  --
  -- In a category `C`, objects `W`, `X`, `Y`, `Z` and morphisms:
  --
  --  `f`: `X -> W`
  --  `g`: `X -> Y`
  --  `h`: `Y -> Z`
  --
  -- determine a polynomial endofunctor from `C/W` to `C/Z` comprised of
  -- the composition (domain to codomain):
  --
  --  `f*`: `C/W -> C/X` (pullback (or "base change") functor of `f`)
  --  `Pi(g)`: `C/X -> C/Y` (dependent product)
  --  `Sigma(h)`: `C/Y -> C/Z` (dependent sum)
  --
  -- (This is an endofunctor iff `W==Z`, and a non-dependent endofunctor
  -- iff furthermore `W==Z==1` (where `1` is the terminal object of `C`).
  PolyFunctorFromMorphisms : (w, x, y, z : object) -> (f, g, h : morphism) ->
    PolynomialFunctorF object morphism

public export
data CartesianTransformationF : Type -> Type -> Type -> Type where
  -- See
  -- https://ncatlab.org/nlab/show/equifibered%20natural%20transformation#properties:
  --
  -- Given a category `C` with a terminal object, a category `D` with all
  -- pullbacks, and a functor `G : C -> D`, then an object `F1` of `C` and
  -- a morphism `F[F1] -> G[1]` (where `1` is the terminal object of `C`)
  -- determine a functor `F : C -> D` and a natural transformation `F -> G`
  -- which is "equifibered" (also called "cartesian"), meaning that all of
  -- its naturality squares are pullbacks.  (The functor `F` itself is
  -- generated by taking pullbacks.)
    CartesianTransformationFromMorphism:
      (f1 : object) -> (f : morphism) -> (g : functor) ->
      CartesianTransformationF object morphism functor

public export
data AdjunctionF : Type -> Type -> Type where
  AdjunctionFromUnits : (l, r : functor) -> (unit, counit : natTrans) ->
    AdjunctionF functor natTrans

public export
data ConjugateNatTransF : Type -> Type where
  -- See
  -- https://unapologetic.wordpress.com/2007/07/30/transformations-of-adjoints/
  -- for the definition of "conjugate natural transformations" and how
  -- they can be used to transform adjoints.
  ConjugateNatTransFromPair :
    natTrans -> natTrans -> ConjugateNatTransF natTrans

-- Expressions are drawn from four categories determined by the presence
-- or absence of each of the following pairs of universal properties:
--
--  - Equalizers & coequalizers
--    (Categories with them are called "refined"; those without are "unrefined")
--  - Initial algebras & terminal coalgebras
--    (Categories with them are "first-order"; those without are "zeroth-order")
--
-- The zeroth-order categories may also be called "substitution" categories.
--
-- All four categories have each of the following pairs of universal properties:
--
--  - Initial objects & terminal objects
--  - Products & coproducts
--
-- All the types until the end of the `Expression` section are zeroth-order,
-- even though they _have_ initial algebras and terminal coalgebras, because
-- they are all defined in the style of "datatypes à la carte" -- in effect,
-- this means that we are programming in the category of polynomial functors
-- of the zeroth-order categories.  At the end of the `Expression` section,
-- we generate the full forms of expressions by taking the fixpoints and
-- cofixpoints of the datatypes previously defined; those types live only in
-- the first-order categories.

--------------------
---- Core types ----
--------------------

-- These types are members of at least the refined first-order category
-- (in some cases they are members of other categories as well).  They
-- may be used to help _define_ even categories which they are not themselves
-- objects of, because the _definitions_ all occur in the refined first-order
-- category.  (In particular, they all have initial algebras and terminal
-- coalgebras, which are present in the first-order categories but not the
-- zeroth-order categories.)

---------------------------------------
---- Refined substitution category ----
---------------------------------------

-- Generate objects of the refined substitution category.
public export
data RSubstObjF :
    (obj, morph : Type) -> (domain, codomain : morph -> obj) -> Type where
  RSubstObjInitial : RSubstObjF obj morph domain codomain

public export
data RefinedExpClass : Type where
  RECl_Object : RefinedExpClass
  RECl_Morphism : RefinedExpClass
  RECl_PolyEndo : RefinedExpClass
  RECl_PolyNatTrans : RefinedExpClass

public export
record RefinedExpCategory_Obj where
  constructor RefinedExpClassTypes

  RECat_Object : Type
  RECat_Morphism : Type
  RECat_PolyEndo : Type
  RECat_PolyNatTrans : Type

  RECat_Morphism_Domain : RECat_Morphism -> RECat_Object
  RECat_Morphism_Codomain : RECat_Morphism -> RECat_Object
  RECat_PolyNatTrans_Domain : RECat_PolyNatTrans -> RECat_PolyEndo
  RECat_PolyNatTrans_Codomain : RECat_PolyNatTrans -> RECat_PolyEndo

public export
record RefinedExpCategory_Equiv (recat : RefinedExpCategory_Obj) where
  constructor RefinedExpCategory_Equivalences

  RECat_Object_Equiv : Type
  RECat_Morphism_Equiv : Type
  RECat_PolyEndo_Equiv : Type
  RECat_PolyNatTrans_Equiv : Type

  RECat_ObjectEquiv_Left :
    RECat_Object_Equiv -> RECat_Object recat
  RECat_ObjectEquiv_Right :
    RECat_Object_Equiv -> RECat_Object recat
  RECat_MorphismEquiv_Left :
    RECat_Morphism_Equiv -> RECat_Morphism recat
  RECat_MorphismEquiv_Right :
    RECat_Morphism_Equiv -> RECat_Morphism recat
  RECat_PolyEndoEquiv_Left :
    RECat_PolyEndo_Equiv -> RECat_PolyEndo recat
  RECat_PolyEndoEquiv_Right :
    RECat_PolyEndo_Equiv -> RECat_PolyEndo recat
  RECat_PolyNatTransEquiv_Left :
    RECat_PolyNatTrans_Equiv -> RECat_PolyNatTrans recat
  RECat_PolyNatTransEquiv_Right :
    RECat_PolyNatTrans_Equiv -> RECat_PolyNatTrans recat

public export
ObjectTypeInterpretation : Type -> Type
ObjectTypeInterpretation obj = obj -> Type

public export
TermTypeInterpretation : {obj : Type} -> ObjectTypeInterpretation obj -> Type
TermTypeInterpretation {obj} objInterp = (a : obj) -> () -> objInterp a

public export
MorphismTypeInterpretation : {obj : Type} -> ObjectTypeInterpretation obj ->
  (morph : Type) -> (domain, codomain : morph -> obj) -> Type
MorphismTypeInterpretation objInterp morph domain codomain =
  (m : morph) -> objInterp (domain m) -> objInterp (codomain m)

public export
MorphHasSig : {obj, morph : Type} ->
  (domain : morph -> obj) -> (codomain : morph -> obj) ->
  morph -> (obj, obj) -> Type
MorphHasSig domain codomain m (a, b) = (domain m = a, codomain m = b)

public export
FunctorObjmap : Type -> Type
FunctorObjmap obj = obj -> obj

public export
FunctorMorphmap : {obj, morph : Type} ->
  (domain : morph -> obj) -> (codomain : morph -> obj) ->
  FunctorObjmap obj -> Type
FunctorMorphmap {obj} {morph} domain codomain objmap =
  (m : morph) ->
  (fm : morph **
   MorphHasSig domain codomain fm (objmap (domain m), objmap (codomain m)))

public export
FunctorTypeInterpretation : {obj, morph : Type} ->
  {domain, codomain : morph -> obj} ->
  (objInterp : ObjectTypeInterpretation obj) ->
  MorphismTypeInterpretation objInterp morph domain codomain ->
  Type -> Type
FunctorTypeInterpretation {obj} {domain} {codomain}
  objInterp morphInterp functor =
    functor ->
      (objmap : FunctorObjmap obj ** FunctorMorphmap domain codomain objmap)

public export
record RefinedExpInterpretation (recat : RefinedExpCategory_Obj) where
  constructor RefinedExpInterpretations
  REInt_Object : ObjectTypeInterpretation (RECat_Object recat)
  REInt_Term : TermTypeInterpretation REInt_Object
  REInt_Morphism :
    MorphismTypeInterpretation
      REInt_Object (RECat_Morphism recat)
      (RECat_Morphism_Domain recat) (RECat_Morphism_Codomain recat)
  REInt_PolyEndo :
    FunctorTypeInterpretation REInt_Object REInt_Morphism (RECat_PolyEndo recat)

public export
record RefinedExpCategoryType where
  constructor RefinedExpCategoryComponents
  REC_Obj : RefinedExpCategory_Obj
  REC_Int : RefinedExpInterpretation REC_Obj

-------------------------------
-------------------------------
---- "Fixed" S-expressions ----
-------------------------------
-------------------------------

public export
ArityMap : Type -> Type
ArityMap atom = atom -> Nat

public export
data FSexpF : {atom : Type} -> ArityMap atom -> Type -> Type where
  FSop : {atom : Type} -> {arity : ArityMap atom} -> {carrier : Type} ->
    (a : atom) -> Tuple (arity a) carrier -> FSexpF {atom} arity carrier

public export
FSexpAlg : {atom : Type} -> ArityMap atom -> Type -> Type
FSexpAlg = Algebra . FSexpF

public export
FreeFSexp : {atom : Type} -> ArityMap atom -> Type -> Type
FreeFSexp = FreeMonad . FSexpF

public export
FreeFSalg : {atom : Type} -> ArityMap atom -> Type -> Type
FreeFSalg = FreeAlgebra . FSexpF

public export
MuFSexp : {atom : Type} -> ArityMap atom -> Type
MuFSexp = Mu . FSexpF

public export
FSexpCoalg : {atom : Type} -> ArityMap atom -> Type -> Type
FSexpCoalg = Coalgebra . FSexpF

public export
CofreeFSexp : {atom : Type} -> ArityMap atom -> Type -> Type
CofreeFSexp = CofreeComonad . FSexpF

public export
CofreeFScoalg : {atom : Type} -> ArityMap atom -> Type -> Type
CofreeFScoalg = CofreeCoalgebra . FSexpF

public export
NuFSexp : {atom : Type} -> ArityMap atom -> Type
NuFSexp = Nu . FSexpF

public export
record FSexpMorphCarrier {atom : Type} (arity : ArityMap atom) where
  constructor FSexpMorphBundle
  FSexpMorph : Type
  FSexpObj : Type
  FSexpDomain : FSexpMorph -> TupleP FSexpObj
  FSexpCodomain : FSexpMorph -> FSexpObj

{-
public export
data FSexpMorphF : {atom : Type} -> {arity : ArityMap atom} ->
    (expCarrier : Type) -> (morphCarrier : Type) ->
    (signature : morphCarrier -> (TupleP expCarrier, expCarrier))
    -}

--------------------------
--------------------------
---- The topos FinSet ----
--------------------------
--------------------------

public export
record FSTCarrier where

-----------------------------------------
---- Refined S-expressions and lists ----
-----------------------------------------

public export
FSexpRefinementAlg : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FSexpRefinementAlg {atom} arity carrier right =
  FSexpF arity (FSexpF arity carrier) -> Either (FreeFSexp arity carrier) right

public export
FSexpRefinement : {atom : Type} -> ArityMap atom -> Type -> Type -> Type
FSexpRefinement arity carrier right =
  FreeFSexp arity carrier -> Either (FreeFSexp arity carrier) right

public export
FreeFSexpRefinementAlg : {atom : Type} -> ArityMap atom ->
  Type -> Type -> Type -> Type
FreeFSexpRefinementAlg arity leftIn leftOut right =
  FreeFSexp arity leftIn -> Either (FreeFSexp arity leftOut) right

-------------------------------------------------
---- S-expressions with natural number atoms ----
-------------------------------------------------

public export
data NSexpClass : Type where
  NSexpNat : NSexpClass
  NSEXP : NSexpClass
  NSLIST : NSexpClass

public export
NSexpObject : Type
NSexpObject = ProductCatObject NSexpClass

public export
data NSexpFunctor : (carrier : NSexpObject) -> NSexpObject where
  NSatomF :
    NatF (carrier NSexpNat) ->
    NSexpFunctor carrier NSexpNat
  NSexpF :
    carrier NSexpNat -> carrier NSLIST ->
    NSexpFunctor carrier NSEXP
  NSlistF :
    ListF (carrier NSEXP) (carrier NSLIST) ->
    NSexpFunctor carrier NSLIST

public export
NSexpType : NSexpClass -> Type
NSexpType = MuProduct NSexpFunctor

public export
NSNat : Type
NSNat = NSexpType NSexpNat

public export
NSexp : Type
NSexp = NSexpType NSEXP

public export
NSList : Type
NSList = NSexpType NSLIST

public export
nsexpCata : ProductFreeCatamorphism NSexpFunctor
nsexpCata v carrier alg type (InFreeProduct type term) = alg type $ case type of
  NSexpNat => nsexpCataNat term
  NSEXP => nsexpCataExp term
  NSLIST => nsexpCataList term
  where
  mutual
    nsexpCataNat :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad NSexpFunctor v) NSexpNat
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSexpNat
    nsexpCataNat (ProductCatTermVar t) = ProductCatTermVar t
    nsexpCataNat (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSatomF a => NSatomF $ case a of
          ZeroF => ZeroF
          SuccF n => case n of
            InFreeProduct NSexpNat n =>
              SuccF $ alg NSexpNat $ nsexpCataNat n

    nsexpCataExp :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad NSexpFunctor v) NSEXP
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSEXP
    nsexpCataExp (ProductCatTermVar v) = ProductCatTermVar v
    nsexpCataExp (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSexpF (InFreeProduct NSexpNat n) l =>
          case l of
            InFreeProduct NSLIST l' =>
              NSexpF
                (alg NSexpNat $ nsexpCataNat n) (alg NSLIST $ nsexpCataList l')

    nsexpCataList :
      ProductCatTermFunctor
        NSexpFunctor v
        (ProductCatFreeMonad NSexpFunctor v) NSLIST
        ->
      ProductCatTermFunctor NSexpFunctor v carrier NSLIST
    nsexpCataList (ProductCatTermVar v) = ProductCatTermVar v
    nsexpCataList (ProductCatTermComposite com) = ProductCatTermComposite $
      case com of
        NSlistF l => NSlistF $ case l of
          NilF => NilF
          ConsF (InFreeProduct NSEXP x) l' =>
            case l' of
              InFreeProduct NSLIST l'' =>
                ConsF
                  (alg NSEXP $ nsexpCataExp x)
                  (alg NSLIST $ nsexpCataList l'')

---------------------------------------------------------
---------------------------------------------------------
---- Interpretation of S-expressions into categories ----
---------------------------------------------------------
---------------------------------------------------------

public export
data UniversalProperty : Type where
  -- Equalizers and coequalizers.
  ConnectedLimits : UniversalProperty
  -- Initial algebras and terminal coalgebras of polynomial endofunctors.
  InductiveTypes : UniversalProperty

public export
data SexpCategory : Type where
  SubstCat : SexpCategory
  RefinedSubstCat : SexpCategory
  ADTCat : SexpCategory
  RefinedADTCat : SexpCategory

public export
hasProperty : UniversalProperty -> SexpCategory -> Bool
hasProperty ConnectedLimits SubstCat = False
hasProperty ConnectedLimits RefinedSubstCat = True
hasProperty ConnectedLimits ADTCat = False
hasProperty ConnectedLimits RefinedADTCat = True
hasProperty InductiveTypes SubstCat = False
hasProperty InductiveTypes RefinedSubstCat = False
hasProperty InductiveTypes ADTCat = True
hasProperty InductiveTypes RefinedADTCat = True

public export
SMorphismInterpretation : Type
SMorphismInterpretation =
  (domain : Type ** codomain : Type ** domain -> codomain)

public export
NatTransInterpretation : Type
NatTransInterpretation =
  (f : Type -> Type ** g : Type -> Type ** (x : Type) -> f x -> g x)

public export
data SexpInterpretation : NSexpClass -> Type where
  SnatAsNat : Nat -> SexpInterpretation NSexpNat
  SexpAsObject : Type -> SexpInterpretation NSEXP
  SexpAsMorphism : SMorphismInterpretation -> SexpInterpretation NSEXP
  SexpAsFunctor : (Type -> Type) -> SexpInterpretation NSEXP
  SexpAsNatTrans : NatTransInterpretation -> SexpInterpretation NSEXP
  SlistAsObjects : List Type -> SexpInterpretation NSLIST
  SlistAsMorphisms :
    List SMorphismInterpretation -> SexpInterpretation NSLIST
  SlistAsFunctors : List (Type -> Type) -> SexpInterpretation NSLIST
  SlistAsNatTrans : List NatTransInterpretation -> SexpInterpretation NSLIST

public export
record SexpCheckResult (inputType : NSexpClass) where
  constructor SexpInterpretations
  Input : NSexpType inputType
  InputInterpretation : Maybe (SexpInterpretation inputType)
  AllInterpretations :
    (type : NSexpClass) -> NSexpType type -> Maybe (SexpInterpretation type)

---------------------
---- Polynomials ----
---------------------

-- A univariate, finite-degree power.
public export
data PowerF : Type -> Type -> Type where
  FactorsF :
    ListF (coefficient, NatF carrier) carrier ->
    PowerF coefficient carrier

public export
Bifunctor PowerF where
  bimap f g (FactorsF l) = FactorsF $ bimap (bimap f $ map g) g l

export
powerFactors :
  PowerF coefficient carrier ->
  ListF (coefficient, NatF carrier) carrier
powerFactors (FactorsF l) = l

-- A univariate, finite-degree polynomial.
public export
data PolynomialF : Type -> Type -> Type where
  PolyTermsF :
    ListF (PowerF coefficient carrier) carrier ->
    PolynomialF coefficient carrier

public export
Bifunctor PolynomialF where
  bimap f g (PolyTermsF t) = PolyTermsF $ bimap (bimap f g) g t

export
polyTerms :
  PolynomialF coefficient carrier ->
  ListF (PowerF coefficient carrier) carrier
polyTerms (PolyTermsF t) = t

export
polyFactors :
  PolynomialF coefficient carrier ->
  ListF (ListF (coefficient, NatF carrier) carrier) carrier
polyFactors = mapFst powerFactors . polyTerms

-- Next, we introduce a way of interpreting polynomials as datatypes.
-- A polynomial endofunctor may be viewed as simply a polynomial, and
-- may be factored into one, but when representing types with
-- endofunctors, we may wish to factor out commonality amongst types
-- and compose them from smaller components. Such types could theoretically
-- be fully distributed into flat polynomials like `PolynomialF`, but
-- when using polynomials as types, we can gain expressivity with explicit
-- composition.
public export
data PolyTypeF : Type -> Type -> Type where
  PolyTypeComposeF : functor -> functor -> PolyTypeF type functor
  PolyTypeADTF : PolynomialF type functor -> PolyTypeF type functor

-- Next, we perform another recursion.  A programming language might define
-- an ADT as an initial algebra of a polynomial endofunctor.  So, we will
-- treat PolynomialF as representative of polynomial endofunctors, and
-- therefore potentially of ADTs.  To turn a polynomial endofunctor
-- which represents a non-recursive datatype into one which represents a
-- recursive type, we apply the above-defined higher-order functor,
-- `FreeMonad` (AKA `F*`).  So to generate polynomial _recursive_ types, we add
-- to `PolynomialF` the option of applying `FreeMonad` to an existing polynomial
-- type.
public export
data PolyRecTypeF : Type -> Type -> Type where
  PolyTypeFreeF :
    functor -> PolyRecTypeF type functor
  PolyRecTypeADTF :
    PolyTypeF type functor -> PolyRecTypeF type functor
