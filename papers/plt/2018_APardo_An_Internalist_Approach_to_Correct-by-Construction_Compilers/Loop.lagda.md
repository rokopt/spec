----------------------------------------------------------------------
-- An Approach to Correct-by-construction Compilers
--
-- Intermediate language
--
----------------------------------------------------------------------


```agda
module Loop where

open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List
open import Data.Product
open import Data.Maybe hiding ( map )
open import Category.Monad
open import Function
open import Data.String renaming (_==_ to _==ₛ_)
open import Common

open import Category.Monad
open import Category.Monad.Indexed
open RawMonadZero -- {lzero} Data.Maybe.monad

-- In the intermediate language we get rid of the distinction between
-- expressions and commands.
data LCode : Set where
  pushₙ : (n : ℕ) → LCode
  add   : LCode
  eq    : LCode
  load  : (x : Var) → LCode
  store : (x : Var) → LCode
  loop  : (c₁ : LCode) → (c₂ : LCode) → LCode
  _,_   : (c₁ : LCode) → (c₂ : LCode) → LCode


-- We will enforce stack-safety through the use of a type-system
-- for stacks (cf. trabajo de Alberto?)
StackType : Set
StackType = List Type

-- A code is safe with respect to two stack-types
data _⊢_↝_ : StackType → LCode → StackType → Set where
  rpushₙ : ∀ {st} {n : ℕ} → st ⊢ pushₙ n ↝ (nat ∷ st)
  radd   : ∀ {st} → (nat ∷ nat ∷ st) ⊢ add ↝ (nat ∷ st)
  req    : ∀ {st} → (nat ∷ nat ∷ st) ⊢ eq ↝ (bool ∷ st)
  rload  : ∀ {st} {x : Var} → st ⊢ load x ↝ (nat ∷ st)
  rstore : ∀ {st} {x : Var} → (nat ∷ st) ⊢ store x ↝ st
  rloop  : ∀ {st} {c₁ c₂} → st ⊢ c₁ ↝ (bool ∷ st) →
                                     st ⊢ c₂ ↝ st →
                                     st ⊢ loop c₁ c₂ ↝ st
  rseq   : ∀ {st st' st''} {c₁ c₂} →
             st ⊢ c₁ ↝ st' → st' ⊢ c₂ ↝ st'' →
             st ⊢ c₁ , c₂ ↝ st''

-- the previous predicate induces an ornament
data LCodeₜ : StackType → StackType → Set where
  pushₙ : ∀ {st} → (n : ℕ) → LCodeₜ st (nat ∷ st)
  add   : ∀ {st} → LCodeₜ (nat ∷ nat ∷ st) (nat ∷ st)
  eq    : ∀ {st} → LCodeₜ (nat ∷ nat ∷ st) (bool ∷ st)
  load  : ∀ {st} → (x : Var) → LCodeₜ st (nat ∷ st)
  store : ∀ {st} → (x : Var) → LCodeₜ (nat ∷ st) st
  loop  : ∀ {st} → (c₁ : LCodeₜ st (bool ∷ st)) →
                   (c₂ : LCodeₜ st st) →
                   LCodeₜ st st
  _,_   : ∀ {st st' st''} →
            (c₁ : LCodeₜ st st') → (c₂ : LCodeₜ st' st'') →
            LCodeₜ st st''

-- and we can lift safe codes to their ornamented version
_⇡cₜ_ : ∀ {st st'} → (c : LCode) → st ⊢ c ↝ st' → LCodeₜ st st'
pushₙ n ⇡cₜ rpushₙ = pushₙ n
add ⇡cₜ radd = add
eq ⇡cₜ req = eq
load x ⇡cₜ rload = load x
store x ⇡cₜ rstore = store x
loop c₁ c₂ ⇡cₜ rloop p₁ p₂ = loop (c₁ ⇡cₜ p₁) (c₂ ⇡cₜ p₂)
(c₁ , c₂) ⇡cₜ rseq p₁ p₂ = (c₁ ⇡cₜ p₁) , (c₂ ⇡cₜ p₂)

-- We can also demote ornamented codes to their raw version
_⇣cₜ : ∀ {st st'} → LCodeₜ st st' → Σ[ lc ∈ LCode ] (st ⊢ lc ↝ st')
pushₙ n ⇣cₜ   = pushₙ n , rpushₙ
add ⇣cₜ       = add , radd
eq ⇣cₜ        = eq , req
load x ⇣cₜ    = load x , rload
store x ⇣cₜ   = store x , rstore
loop c₀ c₁ ⇣cₜ = loop c₀⇣  c₁⇣ , rloop ⊢₀ ⊢₁
  where hi₀ = c₀ ⇣cₜ
        hi₁ = c₁ ⇣cₜ
        c₀⇣ = proj₁ hi₀
        c₁⇣ = proj₁ hi₁
        ⊢₀ = proj₂ hi₀
        ⊢₁ = proj₂ hi₁
(c₀ , c₁) ⇣cₜ  = (c₀⇣ , c₁⇣) , rseq ⊢₀ ⊢₁
  where hi₀ = c₀ ⇣cₜ
        hi₁ = c₁ ⇣cₜ
        c₀⇣ = proj₁ hi₀
        c₁⇣ = proj₁ hi₁
        ⊢₀ = proj₂ hi₀
        ⊢₁ = proj₂ hi₁

open ≡-Reasoning

open import Relation.Binary.HeterogeneousEquality renaming
            (cong to hcong ; cong₂ to hcong₂ ; subst₂ to hsubst₂ ; subst to hsubst)
            hiding (sym ; trans) hiding (inspect ; Reveal_·_is_)

-- Isomorphism
⇡⇣cₜiso : ∀ {st st'} → (c : LCode) → (ct : st ⊢ c ↝ st') →
          (c ⇡cₜ ct) ⇣cₜ ≡ (c , ct)
⇡⇣cₜiso .(pushₙ _) rpushₙ = refl
⇡⇣cₜiso .add radd = refl
⇡⇣cₜiso .eq req = refl
⇡⇣cₜiso .(load _) rload = refl
⇡⇣cₜiso .(store _) rstore = refl
⇡⇣cₜiso .(loop _ _) (rloop {st} {b} {c} bt ct) =
        ≅-to-≡ (≡-×-prop₀ {P = _⊢_↝_} loop (bool ∷_) rloop st b⇣ c⇣ b c ⊢b ⊢c bt ct hib hic)
  where hib : (b ⇡cₜ bt) ⇣cₜ ≡ (b , bt)
        hib = ⇡⇣cₜiso b bt
        hic : (c ⇡cₜ ct) ⇣cₜ ≡ (c , ct)
        hic = ⇡⇣cₜiso c ct
        b⇣ = proj₁ ((b ⇡cₜ bt) ⇣cₜ)
        ⊢b = proj₂ ((b ⇡cₜ bt) ⇣cₜ)
        c⇣ = proj₁ ((c ⇡cₜ ct) ⇣cₜ)
        ⊢c = proj₂ ((c ⇡cₜ ct) ⇣cₜ)

⇡⇣cₜiso {st} {st''} .(_ , _) (rseq {.st} {st'} {.st''} {c₁} {c₂} ct₁ ct₂)
                 = ≅-to-≡ (≡-×-prop _,_ rseq st st' st'' c₁⇣ c₂⇣ c₁ c₂ ⊢₁ ⊢₂ ct₁ ct₂ hi₁ hi₂)
  where hi₁ : (c₁ ⇡cₜ ct₁) ⇣cₜ ≡ (c₁ , ct₁)
        hi₁ = ⇡⇣cₜiso c₁ ct₁
        hi₂ : (c₂ ⇡cₜ ct₂) ⇣cₜ ≡ (c₂ , ct₂)
        hi₂ = ⇡⇣cₜiso c₂ ct₂
        c₁⇣ = proj₁ ((c₁ ⇡cₜ ct₁) ⇣cₜ)
        ⊢₁ = proj₂ ((c₁ ⇡cₜ ct₁) ⇣cₜ)
        c₂⇣ = proj₁ ((c₂ ⇡cₜ ct₂) ⇣cₜ)
        ⊢₂ = proj₂ ((c₂ ⇡cₜ ct₂) ⇣cₜ)


⇣⇡cₜiso : ∀ {st st'} → (c : LCodeₜ st st') →
          uncurry _⇡cₜ_ (c ⇣cₜ) ≡ c
⇣⇡cₜiso (pushₙ n) = refl
⇣⇡cₜiso add = refl
⇣⇡cₜiso eq = refl
⇣⇡cₜiso (load x) = refl
⇣⇡cₜiso (store x) = refl
⇣⇡cₜiso (loop b c) = cong₂ (λ c₀ c₁ → loop c₀ c₁)
                          (⇣⇡cₜiso b) (⇣⇡cₜiso c)
⇣⇡cₜiso (c₀ , c₁) = cong₂ (λ c c' → c , c')
                          (⇣⇡cₜiso c₀) (⇣⇡cₜiso c₁)

-- The dynamic semantics for this language needs a stack
data Stack : StackType → Set where
  ε   : Stack []
  _▹_ : ∀ {t} {st} → (v : ⟦ t ⟧T) → (s : Stack st) → Stack (t ∷ st)

-- A configuration for this language is a stack and a state
Conf : (st : StackType) → Set
Conf st = Stack st × State


-- We use denoational semantics with a clock
DomCₛ : (st : StackType) → (st' : StackType) → Set
DomCₛ st st' = (clock : ℕ) → (sσ : Conf st) → Maybe (Conf st')

-- We endow DomCₛ with an algebra
fpushₙ : ∀ {st} → (n : ℕ) → DomCₛ st (nat ∷ st)
fpushₙ n = λ {clock (s , σ) → just ((n ▹ s) , σ)}

fadd : ∀ {st} → DomCₛ (nat ∷ nat ∷ st) (nat ∷ st)
fadd = λ {clock ((n ▹ (m ▹ s)) , σ) → just (((n + m) ▹ s) , σ)}

feq : ∀ {st} → DomCₛ (nat ∷ nat ∷ st) (bool ∷ st)
feq = λ {clock ((n ▹ (m ▹ s)) , σ) → just (((n ==ₙ m) ▹ s) , σ)}

fload : ∀ {st} → (x : Var) → DomCₛ st (nat ∷ st)
fload x = λ {clock (s , σ) → just ((σ x ▹ s) , σ)}

postulate
  fstore : ∀ {st} → (x : Var) → DomCₛ (nat ∷ st) st
-- fstore x = λ {clock ((n ▹ s) , σ) → just (s , σ [ x ⟶ n ])}

postulate
  floop : ∀ {st} → DomCₛ st (bool ∷ st) → DomCₛ st st →
                 DomCₛ st st
-- floop fb fc zero sσ = nothing
-- floop fb fc (suc clock) sσ = fb (suc clock) sσ >>=
                             -- (λ { ((b ▹ s') , σ') →
                             -- if b then fc (suc clock) (s' , σ') >>= floop fb fc clock
                                  -- else just (s' , σ') })

postulate
  fseqc : ∀ {st st' st''} → DomCₛ st st' → DomCₛ st' st'' →
                          DomCₛ st st''
-- fseqc f₁ f₂ = λ clock sσ → f₁ clock sσ >>= f₂ clock

-- The semantics is given by the algebra
⟪_⟫ : ∀ {st st'} → LCodeₜ st st' → DomCₛ st st'
⟪_⟫ (pushₙ n)   = fpushₙ n
⟪_⟫ add         = fadd
⟪_⟫ eq          = feq
⟪_⟫ (load x)    = fload x
⟪_⟫ (store x)   = fstore x
⟪_⟫ (loop c₁ c₂) = floop ⟪ c₁ ⟫ ⟪ c₂ ⟫
⟪_⟫ (c₁ , c₂)     = fseqc ⟪ c₁ ⟫ ⟪ c₂ ⟫


-- Ornamenting codes with semantics.
--   The constructor substCₛ allows for ornamenting a code
--   with any function which is extensionally equal to the
--   semantics of the code.

EqSem : ∀ {st st'} → DomCₛ st st' → DomCₛ st st' → Set _
EqSem f g = ∀ clock sσ → f clock sσ ≡ g clock sσ

data LCodeₛ : ∀ {st st'} → DomCₛ st st' → Set where
  pushₙ : ∀ {st} → (n : ℕ) → LCodeₛ (fpushₙ {st} n)
  add   : ∀ {st} → LCodeₛ (fadd {st})
  eq    : ∀ {st} → LCodeₛ (feq {st})
  load  : ∀ {st} → (x : Var) → LCodeₛ (fload {st} x)
  store : ∀ {st} → (x : Var) → LCodeₛ (fstore {st} x)
  loop  : ∀ {st} {f₁ f₂} → (c₁ : LCodeₛ f₁) → (c₂ : LCodeₛ f₂) →
                           LCodeₛ (floop {st} f₁ f₂)
  _,c_   : ∀ {st st' st''} {f₁ f₂} →
            (c₁ : LCodeₛ f₁) → (c₂ : LCodeₛ f₂) →
            LCodeₛ (fseqc {st} {st'} {st''} f₁ f₂)
  substCₛ : ∀ {st st'} {f g} → LCodeₛ {st} {st'} f →
                               EqSem f g → LCodeₛ g

_⇡cₛ : ∀ {st st'} → (c : LCodeₜ st st') → LCodeₛ ⟪ c ⟫
pushₙ n ⇡cₛ = pushₙ n
add ⇡cₛ = add
eq ⇡cₛ = eq
load x ⇡cₛ = load x
store x ⇡cₛ = store x
loop b c ⇡cₛ = loop (b ⇡cₛ) (c ⇡cₛ)
(c₁ , c₂) ⇡cₛ = (c₁ ⇡cₛ) ,c (c₂ ⇡cₛ)

_⇣cₛ : ∀ {st st'} {f : DomCₛ st st'} → (c : LCodeₛ f) → LCodeₜ st st'
pushₙ n ⇣cₛ = pushₙ n
add ⇣cₛ = add
eq ⇣cₛ = eq
load x ⇣cₛ = load x
store x ⇣cₛ = store x
loop b c ⇣cₛ = loop (b ⇣cₛ) (c ⇣cₛ)
(c₁ ,c c₂) ⇣cₛ = c₁ ⇣cₛ , c₂ ⇣cₛ
substCₛ c _ ⇣cₛ = c ⇣cₛ


-- If the sequence c₀,c₁ terminates, then both c₀ and c₁ also terminate
postulate
  fseqInv : ∀ {st st₀ st' f₁ f₂ cl} {sσ : Conf st} {sσ' : Conf st'} →
            fseqc {st} {st₀} {st'} f₁ f₂ cl sσ ≡ just sσ' →
            ∃ (λ sσ₀ → f₁ cl sσ ≡ just sσ₀ × f₂ cl sσ₀ ≡ just sσ')
-- fseqInv {f₁ = f₁} {f₂} {clock} {sσ} {sσ'} p with f₁ clock sσ
-- fseqInv {f₁ = f₁} {f₂} {clock} {sσ} {sσ'} p | just sσ₀ = sσ₀ , (refl , p)
-- fseqInv {f₁ = f₁} {f₂} {clock} {sσ} {s'} () | nothing


open import Data.Sum
open Reveal_·_is_

-- If loop b c terminates, then either b computes to false or b
-- computes to true, c terminates, and the recursive call of the
-- loop also terminates.
postulate
  floopInv : ∀ {cl st} {fb : DomCₛ st (bool ∷ st)} {fc : DomCₛ st st} {sσ sσ' : Conf st} →
             floop fb fc (suc cl) sσ ≡ just sσ' →
             ∃₂ (λ sb σb → fb (suc cl) sσ ≡ just (false ▹ sb , σb) × sσ' ≡ (sb , σb))
            ⊎ ∃₂ (λ sb σb → fb (suc cl) sσ ≡ just (true ▹ sb , σb) ×
              ∃ (λ sσc → fc (suc cl) (sb , σb) ≡ just sσc × floop fb fc cl sσc ≡ just sσ'))
-- floopInv {cl} {st} {fb} {fc} {sσ} {sσ'} p with fb (suc cl) sσ
-- floopInv {cl} {st} {fb} {fc} {sσ} {sσ'} () | nothing
-- floopInv {cl} {st} {fb} {fc} {sσ} {sσ'} refl | just ((false ▹ sb) , σb) = inj₁ (sb , σb , refl , refl)
-- ... | just ((true ▹ sb) , σb) with (fc (suc cl) (sb , σb)) | inspect (fc (suc cl)) (sb , σb)
-- floopInv {cl} {st} {fb} {fc} {sσ} {sσ'} () | just ((true ▹ sb) , σb) | nothing | _
-- floopInv {cl} {st} {fb} {fc} {sσ} {sσ'} p | just ((true ▹ sb) , σb) | (just sσc) | [ p' ] =
--                    inj₂ (sb , σb , (refl , (sσc , p' , p)))
```