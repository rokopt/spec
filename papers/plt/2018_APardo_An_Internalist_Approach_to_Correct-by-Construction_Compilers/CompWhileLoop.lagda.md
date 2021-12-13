----------------------------------------------------------------------
-- An Approach to Correct-by-construction Compilers
--
-- Correct compiler from While language to intermediate Loop language
--
----------------------------------------------------------------------


```agda
{-# OPTIONS --allow-unsolved-metas #-}
module CompWhileLoop where

open import Data.Nat
open import Data.Nat.Properties using (+-comm)
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
open import Common
open import While
open import Loop

open import Category.Monad
open import Category.Monad.Indexed
-- open RawMonad {lzero} Data.Maybe.monad


{- Correct-by-construction compiler for expressions -}
postulate
  compₑ : ∀ {t} {f} {st} → Exprₛ {t} f →
                         LCodeₛ {st} (λ {clock (s , σ) → just ((f σ ▹ s) , σ) })
-- compₑ ∣ n ∣ₙ = pushₙ n
-- compₑ (e₁ ⊕ e₂) = compₑ e₂ ,c (compₑ e₁ ,c add)
-- compₑ (e₁ == e₂) = compₑ e₂ ,c (compₑ e₁ ,c eq)
-- compₑ (var x) = load x

correctLCodeF : ∀ {st} → DomSₛ → DomCₛ st st
correctLCodeF f clock (s , σ) = f clock σ >>= (λ σ' → just (s , σ'))


{- Aditional proofs of extensional equality for compilation of while and sequence statements -}
postulate
  eqloop : ∀ {st} fb f → EqSem {st} {st}
                           (floop (λ { clock (s , σ) → just ((fb σ ▹ s) , σ) }) (correctLCodeF f))
                           (correctLCodeF (fwhile fb f))
-- eqloop f₁ f₂ zero sσ = refl
-- eqloop f₁ f₂ (suc clock) (s , σ) with f₁ σ
-- eqloop f₁ f₂ (suc clock) (s , σ) | false = refl
-- eqloop f₁ f₂ (suc clock) (s , σ) | true with (f₂ (suc clock) σ)
-- eqloop f₁ f₂ (suc clock) (s , σ) | true | nothing = refl
-- eqloop f₁ f₂ (suc clock) (s , σ) | true | just σ' = eqloop f₁ f₂ clock (s , σ')

postulate
  eqseq : ∀ {st} f₁ f₂ → EqSem {st} {st}
                           (fseqc (correctLCodeF f₁) (correctLCodeF f₂))
                           (correctLCodeF (λ clock σ → f₁ clock σ >>= f₂ clock))
-- eqseq f₁ f₂ clock (s , σ) with f₁ clock σ
-- eqseq f₁ f₂ clock (s , σ) | nothing = refl
-- eqseq f₁ f₂ clock (s , σ) | just σ' = refl


{- Correct-by-construction compiler for statements -}
postulate
  compₛ : ∀ {f} {st} → Stmtₛ f →
                     LCodeₛ (correctLCodeF {st} f)
-- compₛ (x := e) = compₑ e ,c store x
-- compₛ (while_do_ {fb} {f} eb stmt) = (loop (compₑ eb) (compₛ stmt)) *
  -- where _* : LCodeₛ _ → _
        -- c * = substCₛ c (eqloop fb f)
-- compₛ (_,_ {f₁} {f₂} stmt₁ stmt₂) = (compₛ stmt₁ ,c compₛ stmt₂) *
  -- where _* : LCodeₛ _ → _
        -- c * = substCₛ c (eqseq f₁ f₂)



{- In the externalist approach, we should define the compiler and
   do proofs of stack-safe and correctness. We show this approach only
   for expressions: -}

{- Compiler of expressions -}
compe : Expr → LCode
compe ∣ n ∣ₙ = pushₙ n
compe (e₁ ⊕ e₂) = compe e₁ , compe e₂ , add
compe (e₁ == e₂) = compe e₁ , compe e₂ , eq
compe (var x) = load x

{- Stack-safe proof -}
comp-ty : ∀ {e t} st → ⊢ e ∶ t → st ⊢ compe e ↝ (t ∷ st)
comp-ty st tnat = rpushₙ
comp-ty st (tplus ty ty₁) = rseq (comp-ty st ty) (rseq (comp-ty (nat ∷ st) ty₁) radd)
comp-ty st (teq ty ty₁) = rseq (comp-ty st ty) (rseq (comp-ty (nat ∷ st) ty₁) req)
comp-ty st tvar = rload

{- Correctness proof -}
postulate
  comp-sem : ∀ {e t st} → (ty : ⊢ e ∶ t) → ∀ clock σ (s : Stack st) →
     ⟪ (compe e) ⇡cₜ (comp-ty st ty) ⟫ clock (s , σ) ≡ just ((⟦ e ⇡ₜ ty ⟧ σ ▹ s) , σ)
-- comp-sem tnat clock σ s = refl
-- comp-sem {e ⊕ e₁} (tplus ty ty₁)  clock σ s with comp-sem ty clock σ s
-- ... | q with comp-sem ty₁ clock σ (⟦ e ⇡ₜ ty ⟧ σ  ▹ s)
-- ... | p rewrite q | p = cong just (cong (_, σ) (cong (_▹ s) (+-comm (⟦ e₁ ⇡ₜ ty₁ ⟧ σ) (⟦ e ⇡ₜ ty ⟧ σ))))
-- comp-sem {e == e₁} (teq ty ty₁) clock σ s with comp-sem ty clock σ s
-- ... | q with comp-sem ty₁ clock σ (⟦ e ⇡ₜ ty ⟧ σ  ▹ s)
-- ... | p rewrite q | p = cong just (cong (_, σ) (cong (_▹ s) (==ₙ-sym (⟦ e₁ ⇡ₜ ty₁ ⟧ σ) (⟦ e ⇡ₜ ty ⟧ σ))))
-- comp-sem tvar clock σ s = refl

{- The externalist compiler generates... -}
comp-corr : ∀ {e t} → (ty : ⊢ e ∶ t) →
            Σ[ c ∈ LCode ] -- ...code...
            (∀ st → Σ[ t ∈ (st ⊢ c ↝ (t ∷ st)) ] -- ... well typed and
              (∀ cl σ s → ⟪ c ⇡cₜ t ⟫ cl (s , σ) ≡ just ((⟦ e ⇡ₜ ty ⟧ σ ▹ s) , σ))) -- ... it preserves semantics.
comp-corr {e} ty = compe e , λ st → (comp-ty st ty , comp-sem ty)
```