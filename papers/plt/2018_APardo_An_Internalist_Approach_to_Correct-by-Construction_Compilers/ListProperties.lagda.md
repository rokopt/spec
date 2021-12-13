

```
{-# OPTIONS --allow-unsolved-metas #-}
module ListProperties where

open import Data.List -- hiding ( monad ; map )
open import Data.Nat
open import Data.Maybe -- hiding ( map ; setoid )
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Algebra

import Relation.Binary.Reasoning.Setoid as EqR

-- Lookup
_‼_ : {A : Set} → List A → ℕ → Maybe A
[] ‼ _ = nothing
(a ∷ ls) ‼ zero = just a
(a ∷ ls) ‼ (suc n) = ls ‼ n

_‼+_∷_ : {A : Set} → (as : List A) → (a : A) → (as' : List A) →
            (as ++ a ∷ as') ‼ (length as) ≡ just a
[] ‼+ a ∷ as' = refl
(x ∷ as) ‼+ a ∷ as' = as ‼+ a ∷ as'

len++ : {A : Set} → (c : List A) → (a : A) →
        suc (length c) ≡ length (c ++ [ a ])
len++ [] a = refl
len++ (x ∷ c) a = cong suc (len++ c a)

len++' : {A : Set} → (l₀ l₁ : List A) →
         length (l₀ ++ l₁) ≡ length l₀ + length l₁
len++' [] l₁ = refl
len++' (x ∷ l₀) l₁ = cong suc (len++' l₀ l₁)

open Monoid hiding (refl ; sym ; trans ; setoid ; ε)

postulate
  len++₂ : {A : Set} → (l₀ l₁ l₂ : List A) →
           (a b : A) →
           length (l₀ ++ l₁) + (2 + length l₂) ≡
         length (l₀ ++ l₁ ++ a ∷ l₂ ++ [ b ])
  -- len++₂ {A} l₀ l₁ l₂ a b =
  -- begin
    -- length (l₀ ++ l₁) + (2 + length l₂)
  -- ≈⟨ cong (length (l₀ ++ l₁) +_) (f a b l₂) ⟩
    -- length (l₀ ++ l₁) + length (a ∷ l₂ ++ [ b ])
  -- ≈⟨ sym (len++' (l₀ ++ l₁) (a ∷ l₂ ++ [ b ])) ⟩
    -- length ((l₀ ++ l₁) ++ a ∷ l₂ ++ [ b ])
  -- ≈⟨ cong length (assoc (monoid A) l₀ l₁ (a ∷ l₂ ++ [ b ])) ⟩
    -- length (l₀ ++ l₁ ++ a ∷ l₂ ++ [ b ])
  -- ∎
  -- where f : (a₀ a₁ : A) → (l : List A) →
            -- 2 + length l ≡ length (a₀ ∷ l ++ [ a₁ ])
        -- f _ _ [] = refl
        -- f a₀ a₁ (x ∷ l) = cong suc (f a₀ a₁ l)
        -- open EqR (setoid ℕ)

postulate
  propAssoc++₄ : ∀ {A : Set} {l₁ l₂ l₃ l₄ : List A} →
                l₁ ++ l₂ ++ l₃ ++ l₄ ≡
                (l₁ ++ l₂ ++ l₃) ++ l₄
-- propAssoc++₄ {A} {l₁} {l₂} {l₃} {l₄} =
    -- begin
      -- l₁ ++ l₂ ++ l₃ ++ l₄
    -- ≈⟨ sym (assoc (monoid A) l₁ l₂ (l₃ ++ l₄)) ⟩
      -- (l₁ ++ l₂) ++ l₃ ++ l₄
    -- ≈⟨ sym (assoc (monoid A) (l₁ ++ l₂) l₃ l₄) ⟩
      -- ((l₁ ++ l₂) ++ l₃) ++ l₄
    -- ≈⟨ cong (_++ l₄) (assoc (monoid A) l₁ l₂ l₃) ⟩
      -- (l₁ ++ l₂ ++ l₃) ++ l₄
    -- ∎
    -- where open EqR (setoid (List A))
postulate
  propAssoc++₅ : ∀ {A : Set} {l₀ l₁ l₂ l₃ l₄ : List A} →
                l₀ ++ l₁ ++ l₂ ++ l₃ ++ l₄ ≡
                (l₀ ++ l₁ ++ l₂ ++ l₃) ++ l₄
-- propAssoc++₅ {A} {l₀} {l₁} {l₂} {l₃} {l₄} =
    -- begin
      -- l₀ ++ (l₁ ++ (l₂ ++ l₃ ++ l₄))
    -- ≈⟨ sym (assoc (monoid A) l₀ l₁ (l₂ ++ l₃ ++ l₄)) ⟩
      -- (l₀ ++ l₁) ++ (l₂ ++ l₃ ++ l₄)
    -- ≈⟨ sym (assoc (monoid A) (l₀ ++ l₁) l₂ (l₃ ++ l₄)) ⟩
      -- ((l₀ ++ l₁) ++ l₂) ++ (l₃ ++ l₄)
    -- ≈⟨ sym (assoc (monoid A) ((l₀ ++ l₁) ++ l₂) l₃ l₄) ⟩
      -- (((l₀ ++ l₁) ++ l₂) ++ l₃) ++ l₄
    -- ≈⟨ cong (_++ l₄) (assoc (monoid A) (l₀ ++ l₁) l₂ l₃) ⟩
      -- ((l₀ ++ l₁) ++ (l₂ ++ l₃)) ++ l₄
    -- ≈⟨ cong (_++ l₄) (assoc (monoid A) l₀ l₁ (l₂ ++ l₃)) ⟩
      -- (l₀ ++ l₁ ++ l₂ ++ l₃) ++ l₄
    -- ∎
    -- where open EqR (setoid (List A))

postulate
  pAssoc++ : {A : Set} {l₀ l₁ l₂ l₃ l₄ l₅ : List A} →
             (l₀ ++ l₁ ++ l₂) ++ l₃ ++ (l₄ ++ l₅) ≡
             l₀ ++ (l₁ ++ l₂ ++ l₃ ++ l₄) ++ l₅
-- pAssoc++ {A} {l₀} {l₁} {l₂} {l₃} {l₄} {l₅} =
--          begin
--            (l₀ ++ l₁ ++ l₂) ++ (l₃ ++ l₄ ++ l₅)
--          ≡⟨ cong (_++ (l₃ ++ l₄ ++ l₅)) (sym (assoc (monoid A) l₀ l₁ l₂)) ⟩
--            ((l₀ ++ l₁) ++ l₂) ++ (l₃ ++ l₄ ++ l₅)
--          ≡⟨ assoc (monoid A) (l₀ ++ l₁) l₂ (l₃ ++ l₄ ++ l₅) ⟩
--            (l₀ ++ l₁) ++ (l₂ ++ l₃ ++ l₄ ++ l₅)
--          ≡⟨ assoc (monoid A) l₀ l₁ (l₂ ++ l₃ ++ l₄ ++ l₅) ⟩
--            l₀ ++ (l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅)
--          ≡⟨ cong (l₀ ++_) (propAssoc++₅ {l₀ = l₁} {l₂} {l₃} {l₄} {l₅}) ⟩
--            l₀ ++ (l₁ ++ l₂ ++ l₃ ++ l₄) ++ l₅
--          ∎
--   where open EqR (setoid (List A))

-- open import Data.Nat.Properties.Simple
open import Data.Nat.Properties

propLength++ : {A : Set} → (l₀ l₁ : List A) →
               length (l₀ ++ l₁) ≡ length l₀ + length l₁
propLength++ [] l₁ = refl
propLength++ (a ∷ l₀) l₁ = cong suc (propLength++ l₀ l₁)

prop∸ : {A : Set} → (l₀ l₁ l₂ : List A) → (a : A) →
        length ((l₀ ++ l₁ ++ [ a ]) ++ l₂) ∸
        (length l₁ + length l₂ + 1) ≡ length l₀
prop∸ l₀ l₁ l₂ a =
      begin
        length ((l₀ ++ l₁ ++ [ a ]) ++ l₂) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (_∸ (length l₁ + length l₂ + 1)) (propLength++ (l₀ ++ l₁ ++ [ a ]) l₂) ⟩
        (length (l₀ ++ l₁ ++ [ a ]) + length l₂) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (λ m → (m + length l₂) ∸ (length l₁ + length l₂ + 1))
              (propLength++ l₀ (l₁ ++ [ a ])) ⟩
        (((length l₀) + (length (l₁ ++ [ a ]))) + length l₂) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (λ m → ((length l₀ + m ) + length l₂) ∸ (length l₁ + length l₂ + 1))
              (propLength++ l₁ [ a ]) ⟩
        ((length l₀) + (length l₁ + 1) + length l₂) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (λ m → m ∸ (length l₁ + length l₂ + 1)) (+-assoc (length l₀) (length l₁ + 1) (length l₂)) ⟩
        ((length l₀) + (length l₁ + 1 + length l₂)) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (λ m → (length l₀ + m) ∸ (length l₁ + length l₂ + 1)) (+-assoc (length l₁) 1 (length l₂)) ⟩
        ((length l₀) + (length l₁ + (1 + length l₂))) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (λ m → (length l₀ + (length l₁ + m)) ∸ (length l₁ + length l₂ + 1))
              (+-comm 1 (length l₂)) ⟩
        ((length l₀) + (length l₁ + (length l₂ + 1))) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ cong (λ m → (length l₀ + m) ∸ (length l₁ + length l₂ + 1)) (sym (+-assoc (length l₁) (length l₂) 1)) ⟩
        ((length l₀) + (length l₁ + length l₂ + 1)) ∸
        (length l₁ + length l₂ + 1)
      ≡⟨ m+n∸n≡m (length l₀) (length l₁ + length l₂ + 1) ⟩
        length l₀
       ∎
  where open EqR (setoid ℕ)


propIndex : ∀ {A : Set} {l₀ l₁ l₂ : List A} {a} →
              (l₀ ++ l₁ ++ a ∷ l₂) ‼ (length (l₀ ++ l₁)) ≡ just a
propIndex {A} {[]} {l₁} {l₂} {a} = l₁ ‼+ a ∷ l₂
propIndex {A} {a₀ ∷ l₀} {l₁} {l₂} {a} = propIndex {l₀ = l₀}

```