----------------------------------------------------------------------
-- An Approach to Correct-by-construction Compilers
--
-- Types and functions used by several languages
-- 
----------------------------------------------------------------------
module Common where

open import Data.String renaming (_==_ to _==ₛ_)
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
            renaming (subst to hsubst ; sym to hsym ; cong to hcong ; cong₂ to hcong₂)

Var : Set
Var = String

-- Types for High-Level and Intermediate Language
data Type : Set where
  nat : Type
  bool : Type

⟦_⟧T : Type → Set
⟦ nat ⟧T = ℕ
⟦ bool ⟧T = Bool

-- A simple minded memory, common to the three languages
State : Set
State = Var → ℕ

_[_⟶_] : State → Var → ℕ → State
σ [ x ⟶ n ] = λ y → if y ==ₛ x then n else σ y

_==ₙ_ : ℕ → ℕ → Bool
zero ==ₙ zero = true
zero ==ₙ suc m = false
suc n ==ₙ zero = false
suc n ==ₙ suc m = n ==ₙ m

==ₙ-sym : ∀ m n → m ==ₙ n ≡ n ==ₙ m
==ₙ-sym zero zero = refl
==ₙ-sym zero (suc n) = refl
==ₙ-sym (suc m) zero = refl
==ₙ-sym (suc m) (suc n) = ==ₙ-sym m n

×-≡ : {A : Set} {B : A → Set} {a : A} {b : B a} {c : Σ A B} → (a , b) ≡ c →
    Σ[ eq ∈ proj₁ c ≡ a ] (proj₂ c ≡ subst B (sym eq) b)
×-≡ {a = a} {b} {.(a , b)} refl = refl , refl

≡-× : {A : Set} {B : A → Set} {a : A} {b : B a} {c : Σ A B} → (eq : a ≡ proj₁ c) →
  b ≡ subst B (sym eq) (proj₂ c) → (a , b) ≡ c
≡-× {a = .a} {.b} {a , b} refl refl = refl

≡-×-prop₀ : {A : Set} {I : Set} {P : I → A → I → Set} →
           (_⊕_ : A → A → A) → (fi : I → I) → 
           (_⊗_ : ∀ {i} {a a'} → P i a (fi i) → P i a' i → P i (a ⊕ a') i) →
           (i : I) → (a a' b b' : A) → (p : P i a (fi i)) → (p' : P i a' i) →
           (q : P i b (fi i)) → (q' : P i b' i) → (eq₁ : (a , p) ≡ (b , q)) →
           (eq₂ : (a' , p') ≡ (b' , q')) →
           ( _,_ {B = λ a₀ → P i a₀ i} (a ⊕ a') (p ⊗ p')) ≅ (b ⊕ b' , q ⊗ q')
≡-×-prop₀ _⊕_ _⊗_ fi i a a' b b' p p' q q' refl refl =
             hcong₂ _,_ refl refl


≡-×-prop : {A : Set} {I : Set} {P : I → A → I → Set} →
           (_⊕_ : A → A → A) →
           (_⊗_ : ∀ {i i' i'' a a'} → P i a i' → P i' a' i'' → P i (a ⊕ a') i'') →
           (i i' i'' : I) → (a a' b b' : A) → (p : P i a i') → (p' : P i' a' i'') →
           (q : P i b i') → (q' : P i' b' i'') → (eq₁ : (a , p) ≡ (b , q)) →
           (eq₂ : (a' , p') ≡ (b' , q')) →
           ( _,_ {B = λ a₀ → P i a₀ i''} (a ⊕ a') (p ⊗ p')) ≅ (b ⊕ b' , q ⊗ q')
≡-×-prop _⊕_ _⊗_ i i' i'' a a' b b' p p' q q' refl refl =
             hcong₂ _,_ refl refl
           
