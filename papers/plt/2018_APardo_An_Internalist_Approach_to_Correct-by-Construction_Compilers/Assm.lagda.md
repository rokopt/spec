----------------------------------------------------------------------
-- An Approach to Correct-by-construction Compilers
--
-- Low-level language
--
----------------------------------------------------------------------

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module Assm where

open import Data.Nat
open import Algebra
open import Data.List renaming (map to lmap)
open import Data.Maybe -- hiding (setoid)
open import Function
open import Data.Product
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.String renaming (_==_ to _==ₛ_) hiding (_++_ ; _≟_ ; length)
open import Data.Bool hiding (_≟_)
open import Common
open import ListProperties

-- Jumps are relative
data Shift : Set where
  left  : ℕ → Shift
  right : ℕ → Shift

-- Codes are list of instructions
data Instr : Set where
  push : ℕ → Instr
  add  : Instr
  eq   : Instr
  jmp  : (i : Shift) → Instr
  jz   : (i : Shift) → Instr
  load : (x : Var) → Instr
  store : (x : Var) → Instr
  nop : Instr

Assm : Set
Assm = List Instr

-- Stacks are lists of numbers
StackJ : Set
StackJ = List ℕ


-- A configuration consists of the program counter, the memory, and
-- the stack
Machine : Set
Machine = ℕ × State × StackJ


pc : Machine → ℕ
pc (i , _ , _) = i


{- Conversion from typed Stack to untyped -}
unty : {t : Type } → ⟦ t ⟧T → ℕ
unty {nat} n = n
unty {bool} false = 0
unty {bool} true = 1


-- Semantics of non-conditional jumps
fjmp : Shift → Machine → Machine
fjmp (left i) (k , σ , s) = k ∸ i , σ , s
fjmp (right i) (k , σ , s) = k + i , σ , s

-- Small-step semantics for configurations
data 【_】_⇝ᵢ_ : Instr → Machine → Machine → Set where
  ⇝nop  : ∀ {k σ s} → 【 nop 】 (k , σ , s) ⇝ᵢ (suc k , σ , s)
  ⇝push  : ∀ {k σ s n} → 【 push n 】 (k , σ , s) ⇝ᵢ (suc k , σ , n ∷ s)
  ⇝add   : ∀ {k σ s n₁ n₂} →
           【 add 】 (k , σ , n₁ ∷ n₂ ∷ s) ⇝ᵢ (suc k , σ , n₁ + n₂ ∷ s)
  ⇝eq    : ∀ {k σ s n₁ n₂} →
           【 eq 】 (k , σ , n₁ ∷ n₂ ∷ s) ⇝ᵢ (suc k , σ , unty (n₁ ==ₙ n₂) ∷ s)
  ⇝jmp   : ∀ {conf sh} →
            【 jmp sh 】 conf ⇝ᵢ (fjmp sh conf)
  ⇝jz0   : ∀ {k σ s sh} →
            【 jz sh 】 (k , σ , 0 ∷ s) ⇝ᵢ (fjmp sh (k , σ , s))
  ⇝jzs   : ∀ {k σ s sh n} →
            【 jz sh 】 (k , σ , suc n ∷ s) ⇝ᵢ
                        (suc k , σ , s)
  ⇝load  : ∀ {k σ s x} → 【 load x 】 (k , σ , s) ⇝ᵢ (suc k , σ , σ x ∷ s)
  ⇝store : ∀ {k σ s x n} → 【 store x 】 (k , σ , n ∷ s) ⇝ᵢ
                                        ((suc k) , ({! [_→_]_ !}) , s)


{- Transitive closure of a relation -}
data Tr  {A : Set} (R : A → A → Set) : A → A → Set where
  ⇝s : ∀ {a b} → R a b → Tr R a b
  _⇝t_ : ∀ {a b c} → R a b → Tr R b c → Tr R a c


{- Single-step semantics for codes. Notice that the code is a
   parameter: it won't change along the execution. -}
data 【_】_⇝_ (c : Assm) : Machine → Machine → Set where
  step : ∀ {i cf cf'} → (c ‼ (pc cf) ≡ just i) →
          【 i 】 cf ⇝ᵢ cf' →  【 c 】 cf ⇝ cf'

{- Transitive closure of sintgle-step semantics -}
【_】_⇝*_ : (is : Assm) → Machine → Machine → Set
【 is 】 cf ⇝* cf' = Tr (【 is 】_⇝_) cf cf'


_⇝t◂_ : ∀ {c cf₁ cf₂ cf₃} →
          【 c 】 cf₁ ⇝* cf₂ →  【 c 】 cf₂ ⇝ cf₃ → 【 c 】 cf₁ ⇝* cf₃
(⇝s st) ⇝t◂ step'  = st ⇝t (⇝s step')
(st ⇝t  trace) ⇝t◂ step' = st ⇝t (trace ⇝t◂ step')

_⇝++_ : ∀ {c cf₁ cf₂ cf₃} →
        【 c 】 cf₁ ⇝* cf₂ →  【 c 】 cf₂ ⇝* cf₃ → 【 c 】 cf₁ ⇝* cf₃
(⇝s st) ⇝++ trace' = st ⇝t trace'
(st ⇝t trace) ⇝++ trace' = st ⇝t (trace ⇝++ trace')


open Monoid hiding (refl ; sym ; trans ; setoid)

postulate
  prop++₁ : ∀ {A : Set} {l₁ l₂ l₃ l₄} →
            l₁ ++ (l₂ ++ (l₃ ++ l₄)) ≡ l₁ ++ ((l₂ ++ l₃) ++ l₄)
-- prop++₁ {A} {l₁} {l₂} {l₃} {l₄} = cong₂  _++_ (refl {x = l₁}) (sym (assoc (monoid A) l₂ l₃ l₄))

-- import Relation.Binary.EqReasoning as EqR

postulate
  prop++₂ : ∀ {A : Set} {l₁ l₂ l₃ l₄} →
            (l₁ ++ l₂) ++ l₃ ++ l₄ ≡ l₁ ++ (l₂ ++ l₃) ++ l₄
-- prop++₂ {A} {l₁} {l₂} {l₃} {l₄} =
  --           begin
  --             (l₁ ++ l₂) ++ l₃ ++ l₄
  --            ≈⟨ assoc (monoid A) l₁ l₂ (l₃ ++ l₄) ⟩
  --             l₁ ++ l₂ ++ l₃ ++ l₄
  --            ≈⟨ prop++₁ {A} {l₁} {l₂} ⟩
  --             l₁ ++ (l₂ ++ l₃) ++ l₄
  --            ∎
  -- where open EqR (setoid (List A))

postulate
  prop++₃ : ∀ {A : Set} {l₁ l₂ l₃ l₄ l₅} →
            l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ ≡ l₁ ++ (l₂ ++ l₃ ++ l₄ ++ l₅)
-- prop++₃ {A} {l₁} {l₂} {l₃} {l₄} {l₅} =
--             begin
--               l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅
--              ≈⟨ refl ⟩
--               l₁ ++ (l₂ ++ l₃ ++ l₄ ++ l₅)
--              ∎
  -- where open EqR (setoid (List A))


postulate
  ⇝++subst : ∀ {γ c₁ c₂ γ' s s' s''} →
      【 γ ++ c₁ ++ (c₂ ++ γ') 】 (length γ , s) ⇝* (length (γ ++ c₁) , s') →
      【 (γ ++ c₁) ++ c₂ ++ γ' 】 (length (γ ++ c₁) , s') ⇝* (length ((γ ++ c₁) ++ c₂) , s'') →
      【 γ ++ (c₁ ++ c₂) ++ γ' 】 (length γ , s) ⇝* (length ((γ ++ c₁) ++ c₂) , s'')
-- ⇝++subst {γ} {c₁} {c₂} {γ'} {s} {s'} {s''} tr₁ tr₂ =
--      _⇝++_ (subst (λ c → 【 c 】 (length γ , s) ⇝* (length (γ ++ c₁) , s'))
--           (prop++₁ {l₁ = γ} {c₁}) tr₁)
--           (subst (λ c → 【 c 】 (length (γ ++ c₁) , s') ⇝* (length ((γ ++ c₁) ++ c₂) , s''))
--           (prop++₂ {l₁ = γ}) tr₂)


{-
-- The small-step semantics for codes is given by the transitive
-- closure of the previous relation.
data 【_】_⇝〔_〕_ (c : Assm) : Machine → ℕ → Machine → Set where
  ⇝c1 : ∀ {conf conf'} → 【 c 】 conf ⇝ conf' → 【 c 】 conf ⇝〔 1 〕 conf'
  ⇝cn : ∀ {conf conf₀ conf' n} →
           【 c 】 conf ⇝ conf₀ → 【 c 】 conf₀ ⇝〔 n 〕 conf' →
--            【 c 】 conf ⇝〔 suc n 〕 conf'


-- ⇝cn◂ : ∀ {c conf conf₀ conf' n} →
--          【 c 】 conf ⇝〔 n 〕 conf₀ → 【 c 】 conf₀ ⇝ conf' →
--          【 c 】 conf ⇝〔 suc n 〕 conf'
-- ⇝cn◂ (⇝c1 x) p = ⇝cn x (⇝c1 p)
-- ⇝cn◂ (⇝cn x pn) p = ⇝cn x (⇝cn◂ pn p)


-- 【_】_⇝⋆_ : Assm → Machine → Machine → Set
-- 【 c 】 conf ⇝⋆ conf' = Σ[ n ∈  ℕ ] 【 c 】 conf ⇝〔 n 〕 conf'

-- ⇝〔〕++ : ∀ {c conf₁ conf₂ conf₃ n₁ n₂}→
--            【 c 】 conf₁ ⇝〔 n₁ 〕 conf₂ → 【 c 】 conf₂ ⇝〔 n₂ 〕 conf₃ →
--            【 c 】 conf₁ ⇝〔 n₁ + n₂ 〕 conf₃
-- ⇝〔〕++ {n₁ = zero} () tr₂
-- ⇝〔〕++ {n₁ = suc zero} (⇝c1 x) tr₂ = ⇝cn x tr₂
-- ⇝〔〕++ {n₁ = suc zero} (⇝cn x ()) tr₂
-- ⇝〔〕++ {n₁ = suc (suc n₁)} (⇝cn x tr₁) tr₂ = ⇝cn x (⇝〔〕++ tr₁ tr₂)


-- ⇝⋆◂ : ∀ {c s s' s'' k j l} →
--       【 c 】 (k , s) ⇝⋆ (j , s') →
--       【 c 】 (j , s') ⇝ (l , s'') →
--       【 c 】 (k , s) ⇝⋆ (l , s'')
-- ⇝⋆◂ (n , tr) step = suc n , ⇝cn◂ tr step

-- ⇝⋆+ : ∀ {c s s' s'' k j l} →
--       【 c 】 (k , s) ⇝⋆ (j , s') →
--       【 c 】 (j , s') ⇝⋆ (l , s'') →
--       【 c 】 (k , s) ⇝⋆ (l , s'')
-- ⇝⋆+ (n₁ , tr₁) (n₂ , tr₂) = (n₁ + n₂) , (⇝〔〕++ tr₁ tr₂)

-- open Monoid hiding (refl ; sym ; trans ; setoid)

-- prop++₁ : ∀ {A : Set} {l₁ l₂ l₃ l₄} →
--             l₁ ++ (l₂ ++ (l₃ ++ l₄)) ≡ l₁ ++ ((l₂ ++ l₃) ++ l₄)
-- prop++₁ {A} {l₁} {l₂} {l₃} {l₄} = cong₂  _++_ (refl {x = l₁}) (sym (assoc (monoid A) l₂ l₃ l₄))

-- import Relation.Binary.EqReasoning as EqR

-- prop++₂ : ∀ {A : Set} {l₁ l₂ l₃ l₄} →
--             (l₁ ++ l₂) ++ l₃ ++ l₄ ≡ l₁ ++ (l₂ ++ l₃) ++ l₄
-- prop++₂ {A} {l₁} {l₂} {l₃} {l₄} =
--             begin
--               (l₁ ++ l₂) ++ l₃ ++ l₄
--              ≈⟨ assoc (monoid A) l₁ l₂ (l₃ ++ l₄) ⟩
--               l₁ ++ l₂ ++ l₃ ++ l₄
--              ≈⟨ prop++₁ {A} {l₁} {l₂} ⟩
--               l₁ ++ (l₂ ++ l₃) ++ l₄
--              ∎
--   where open EqR (setoid (List A))

-- prop++₃ : ∀ {A : Set} {l₁ l₂ l₃ l₄ l₅} →
--             l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ ≡ l₁ ++ (l₂ ++ l₃ ++ l₄ ++ l₅)
-- prop++₃ {A} {l₁} {l₂} {l₃} {l₄} {l₅} =
--             begin
--               l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅
--              ≈⟨ refl ⟩
--               l₁ ++ (l₂ ++ l₃ ++ l₄ ++ l₅)
--              ∎
--   where open EqR (setoid (List A))


-- ⇝⋆++ : ∀ {γ c₁ c₂ γ' s s' s''} →
--       【 γ ++ c₁ ++ (c₂ ++ γ') 】 (length γ , s) ⇝⋆ (length (γ ++ c₁) , s') →
--       【 (γ ++ c₁) ++ c₂ ++ γ' 】 (length (γ ++ c₁) , s') ⇝⋆ (length ((γ ++ c₁) ++ c₂) , s'') →
--       【 γ ++ (c₁ ++ c₂) ++ γ' 】 (length γ , s) ⇝⋆ (length ((γ ++ c₁) ++ c₂) , s'')
-- ⇝⋆++ {γ} {c₁} {c₂} {γ'} {s} {s'} {s''} tr₁ tr₂ =
--      ⇝⋆+ (subst (λ c → 【 c 】 (length γ , s) ⇝⋆ (length (γ ++ c₁) , s'))
--           (prop++₁ {l₁ = γ} {c₁}) tr₁)
--           (subst (λ c → 【 c 】 (length (γ ++ c₁) , s') ⇝⋆ (length ((γ ++ c₁) ++ c₂) , s''))
--           (prop++₂ {l₁ = γ}) tr₂)

-- -}
```