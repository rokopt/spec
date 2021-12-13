----------------------------------------------------------------------
-- An Approach to Correct-by-construction Compilers
--
-- High-level Language
--
----------------------------------------------------------------------


```
{-# OPTIONS --allow-unsolved-metas #-}
module While where

open import Common
open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List -- hiding ( monad ; map )
open import Data.Product
open import Data.Maybe hiding ( map )
open import Category.Monad
open import Function
open import Data.String renaming (_==_ to _==ₛ_)

-- Expressions
data Expr : Set where
  ∣_∣ₙ : ℕ → Expr
  _⊕_ : (e₁ : Expr) → (e₂ : Expr) → Expr
  _==_ : (e₁ : Expr) → (e₂ : Expr) → Expr
  var  : Var → Expr

-- Commands
data Stmt : Set where
  _:=_ : Var → Expr → Stmt
  while_do'_ : Expr → Stmt → Stmt
  _,_  : Stmt → Stmt → Stmt


-- Typing relation
data ⊢_∶_ : Expr → Type → Set where
  tnat  : ∀ {n} → ⊢ ∣ n ∣ₙ ∶ nat
  tplus : ∀ {e₁ e₂} → ⊢ e₁ ∶ nat → ⊢ e₂ ∶ nat →
                      ⊢ e₁ ⊕ e₂ ∶ nat
  teq   : ∀ {e₁ e₂} → ⊢ e₁ ∶ nat → ⊢ e₂ ∶ nat →
                       ⊢ e₁ == e₂ ∶ bool
  tvar  : ∀ {x} → ⊢ var x ∶ nat

-- Well-formed commands
data ⊢_ : Stmt → Set where
  tassgn : ∀ {x} {e} → ⊢ e ∶ nat → ⊢ (x := e)
  twhile : ∀ {e} {stmt} → ⊢ e ∶ bool →
                          ⊢ stmt → ⊢ (while e do' stmt)
  tseq   : ∀ {stmt₁ stmt₂} → ⊢ stmt₁ → ⊢ stmt₂ → ⊢ (stmt₁ , stmt₂)


-- Ornament for typing
data Exprₜ : Type → Set where
  ∣_∣ₙ : ℕ → Exprₜ nat
  _⊕_ : (e₁ : Exprₜ nat) →
        (e₂ : Exprₜ nat) →
        Exprₜ nat
  _==_ : (e₁ : Exprₜ nat) →
         (e₂ : Exprₜ nat) →
         Exprₜ bool
  var  : (x : Var) → Exprₜ nat

-- A well-typed expression can be lifted
_⇡ₜ_ : ∀ {t} → (e : Expr) → ⊢ e ∶ t → Exprₜ t
∣ x ∣ₙ ⇡ₜ tnat = ∣ x ∣ₙ
(e₁ ⊕ e₂) ⇡ₜ tplus p₁ p₂ = (e₁ ⇡ₜ p₁) ⊕ (e₂ ⇡ₜ p₂)
(e₁ == e₂) ⇡ₜ teq p₁ p₂ = (e₁ ⇡ₜ p₁) == (e₂ ⇡ₜ p₂)
var x ⇡ₜ tvar = var x

-- Ornament for well-formed statements
data Stmtₜ : Set where
  _:=_ : Var → Exprₜ nat → Stmtₜ
  while_do'_ : Exprₜ bool → Stmtₜ → Stmtₜ
  _,_  : Stmtₜ → Stmtₜ → Stmtₜ

postulate
  _⇡stmtₜ_ : (stmt : Stmt) → ⊢ stmt → Stmtₜ
-- (x := e) ⇡stmtₜ tassgn p = x := (e ⇡ₜ p)
-- _⇡stmtₜ_ (while e do stmt) (twhile ebool p) = while e ⇡ₜ ebool do (stmt ⇡stmtₜ p)
-- _⇡stmtₜ_ (stmt₁ , stmt₂) (tseq p₁ p₂) = stmt₁ ⇡stmtₜ p₁ , stmt₂ ⇡stmtₜ p₂


-- Semantics

-- Semantic domain for expressions
DomEₛ : Type → Set
DomEₛ t = (σ : State) → ⟦ t ⟧T

-- We endow DomEₛ with an algebra for expressions
fcnat : ℕ → DomEₛ nat
fcnat n = const n

fplus : DomEₛ nat → DomEₛ nat → DomEₛ nat
fplus f₁ f₂ = λ σ → f₁ σ + f₂ σ

f== : DomEₛ nat → DomEₛ nat → DomEₛ bool
f== f₁ f₂ = λ σ → f₁ σ ==ₙ f₂ σ

fvar : Var → DomEₛ nat
fvar x = λ σ → σ x

-- The semantics of well-typed expressions is given by the algebra
⟦_⟧ : ∀ {t} → Exprₜ t → DomEₛ t
⟦ ∣ n ∣ₙ ⟧ = fcnat n
⟦ e₁ ⊕ e₂ ⟧ = fplus ⟦ e₁ ⟧ ⟦ e₂ ⟧
⟦ e₁ == e₂ ⟧ = f== ⟦ e₁ ⟧ ⟦ e₂ ⟧
⟦ var x ⟧ = fvar x

open import Category.Monad
open import Category.Monad.Indexed
-- open RawMonad {lzero} Data.Maybe.monad

-- Semantic domain for commands
DomSₛ : Set
DomSₛ = (clock : ℕ) → (σ : State) → Maybe State

-- We turn DomSₛ with an algebra for commands
postulate
  fassgn : Var → DomEₛ nat → DomSₛ
-- fassgn x fe = λ clock σ → just (σ [ x ⟶ fe σ ])

fwhile : DomEₛ bool → DomSₛ → DomSₛ
fwhile fb fc zero σ = nothing
fwhile fb fc (suc clock) σ = if fb σ then fc (suc clock) σ >>= fwhile fb fc clock
                                     else just σ

fseq : DomSₛ → DomSₛ → DomSₛ
fseq f₁ f₂ = λ clock σ → f₁ clock σ >>= f₂ clock

-- The semantics is, again, given by the algebra
postulate
  ⟦_⟧ₛ_∣_ : Stmtₜ → DomSₛ
-- ⟦_⟧ₛ_∣_ (x := e) = fassgn x ⟦ e ⟧
-- ⟦_⟧ₛ_∣_ (while eb do stmt) = fwhile ⟦ eb ⟧ (⟦_⟧ₛ_∣_ stmt)
-- ⟦_⟧ₛ_∣_ (stmt₁ , stmt₂) = fseq (⟦_⟧ₛ_∣_ stmt₁) (⟦_⟧ₛ_∣_ stmt₂)


-- Ornamenting expressions with its semantics
data Exprₛ : ∀ {t} → DomEₛ t → Set where
  ∣_∣ₙ : (n : ℕ) → Exprₛ (fcnat n)
  _⊕_ : ∀ {f₁ f₂} →
          (e₁ : Exprₛ f₁) → (e₂ : Exprₛ f₂) →
          Exprₛ (fplus f₁ f₂)
  _==_ : ∀ {f₁ f₂} →
          (e₁ : Exprₛ f₁) → (e₂ : Exprₛ f₂) →
          Exprₛ (f== f₁ f₂)
  var  : (x : Var) → Exprₛ (fvar x)

-- Lifting of well-typed expressions to its semantics
_⇡ₛ : ∀ {t} → (e : Exprₜ t) → Exprₛ ⟦ e ⟧
∣ x ∣ₙ ⇡ₛ = ∣ x ∣ₙ
(e ⊕ e₁) ⇡ₛ = (e ⇡ₛ) ⊕ (e₁ ⇡ₛ)
(e == e₁) ⇡ₛ = (e ⇡ₛ) == (e₁ ⇡ₛ)
(var x) ⇡ₛ = var x

-- The composition of liftings is a lifting
_⇡ₜₛ_ : ∀ {t} → (e : Expr) → (p : ⊢ e ∶ t) → Exprₛ (⟦ e ⇡ₜ p ⟧)
e ⇡ₜₛ p = (e ⇡ₜ p) ⇡ₛ


-- We replay the same for commands
data Stmtₛ : DomSₛ → Set where
  _:=_ : ∀ {f} → (x : Var) → Exprₛ f → Stmtₛ (fassgn x f)
  while_do'_ : ∀ {fb} {f} → Exprₛ fb → Stmtₛ f → Stmtₛ (fwhile fb f)
  _,_  : ∀ {f₁ f₂} → Stmtₛ f₁ → Stmtₛ f₂ → Stmtₛ (fseq f₁ f₂)

postulate
  _⇡stmtₛ : (stmt : Stmtₜ) → Stmtₛ (⟦_⟧ₛ_∣_ stmt)
-- (x := e) ⇡stmtₛ = x := (e ⇡ₛ)
-- (while eb do stmt) ⇡stmtₛ = while (eb ⇡ₛ) do (stmt ⇡stmtₛ)
-- (stmt₁ , stmt₂) ⇡stmtₛ = (stmt₁ ⇡stmtₛ , stmt₂ ⇡stmtₛ)

_⇡stmtₜₛ_ : (stmt : Stmt) → (p : ⊢ stmt) → Stmtₛ (⟦_⟧ₛ_∣_ (stmt ⇡stmtₜ p))
stmt ⇡stmtₜₛ p = (stmt ⇡stmtₜ p) ⇡stmtₛ
```