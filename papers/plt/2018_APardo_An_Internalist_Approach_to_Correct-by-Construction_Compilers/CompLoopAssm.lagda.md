----------------------------------------------------------------------
-- An Approach to Correct-by-construction Compilers
--
-- Correct compiler from While language to intermediate Loop language
-- 
----------------------------------------------------------------------

```agda
{-# OPTIONS --allow-unsolved-metas --termination-depth=2 #-}

module CompLoopAssm where

open import Data.Nat renaming (_≟_ to _≟n_)
open import Data.Bool hiding (_≟_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.List 
open import Data.Product -- hiding (,_)
open import Data.Maybe hiding ( map )
open import Category.Monad
open import Data.Sum
open import Function
open import Data.String renaming (_==_ to _==ₛ_) hiding (_++_ ; length; _≟_)
open import Common
open import Loop
open import Assm
open import Algebra
open import ListProperties

open import Category.Monad
open import Category.Monad.Indexed
open RawMonadZero -- {lzero} Data.Maybe.monad

import Relation.Binary.Reasoning.Setoid as EqR

labEnd : Assm → Shift
labEnd c = right (2 + (length c))

labInit : Assm → Assm → Shift
labInit b c = left ((length b) + (length c) + 1)  

{- Assm code for compiling loop -}
loopAssm : Assm → Assm → Assm
loopAssm isB isC   = isB ++ [ jz le ] ++ isC ++ [ jmp li ]
  where  le   = right (2 + length isC)
         li   = left (1 + length isB + length isC)  

{- Compiler from intermediate Loop language to Jump language -}
compₗ : ∀ {st st'} {f : DomCₛ st st'} → LCodeₛ f → Assm
compₗ (pushₙ n) = [ push n ]
compₗ add = [ add ]
compₗ eq = [ eq ]
compₗ (loop b c) = loopAssm (compₗ b) (compₗ c)
compₗ (c₀ ,c c₁) = (compₗ c₀) ++ (compₗ c₁)
compₗ (load x) = [ load x ]
compₗ (store x) = [ store x ]
compₗ (substCₛ c p) = (compₗ c)


unty* : ∀ {st} → Stack st → List ℕ
unty* ε = []
unty* (v ▹ stack) = unty v ∷ unty* stack


-- import Relation.Binary.EqReasoning as EqR


substInstr : ∀ {γ γ'} → (i : Instr) → (s s' : StackJ) → (σ σ' : State) →
                    【 i 】(length γ , σ , s) ⇝ᵢ (suc (length γ) , σ' , s') → 
                    【 γ ++ [ i ] ++ γ' 】 (length γ , σ , s) ⇝*
                    (length (γ ++ [ i ]) , σ' , s')
substInstr {γ} {γ'} i s s' σ σ' t =
           subst (λ a → 【 γ ++ [ i ] ++ γ' 】 (length γ , σ , s) ⇝*
                                               (a , σ' , s'))
                 (len++ γ i) (⇝s (step (γ ‼+ i ∷ γ') t))

{- Preservation of semantics -}


module correctLoopFalse {b c s σ sb σb γ γ'}
        (hib : 【 γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ] ++ γ' 】
               (length γ , σ , s) ⇝*
               (length (γ ++ b) , σb , 0 ∷ sb)) where

  le : Shift
  le = labEnd c

  li : Shift
  li = labInit b c

  prop : ((γ ++ (b ++ jz le ∷ c ++ jmp li ∷ []) ++ γ') ‼
             length (γ ++ b)) ≡ just (jz le)
  prop = subst (λ l → ((γ ++ l) ‼ length (γ ++ b)) ≡ just (jz le))
               (propAssoc++₅ {l₀ = b} {[ jz le ]} {c})
               (propIndex {l₀ = γ} {b} {c ++ jmp li ∷ γ'})

  tr₁ : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】
           (length γ , σ , s) ⇝*
           (length (γ ++ b) , σb , 0 ∷ sb)
  tr₁ = subst (λ c₀ → 【 γ ++ c₀ 】 length γ , σ , s ⇝*
                       (length (γ ++ b) , σb , 0 ∷ sb))
                       (propAssoc++₅ {l₀ = b} {[ jz le ]} {c})
                       hib

  tr₂ : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】
           (length (γ ++ b) , σb , 0 ∷ sb) ⇝
           (length (γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) , σb , sb)
  tr₂ = subst (λ n₀ → 【 γ ++ (b ++ jz le ∷ c ++ jmp li ∷ []) ++ γ' 】
              length (γ ++ b) , σb , 0 ∷ sb ⇝ (n₀ , σb , sb))
              (len++₂ γ b c (jz le) (jmp li))
              (step prop ⇝jz0)


  correctFalse : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】
                   (length γ , σ , s) ⇝*
                   (length (γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) , σb , sb)
  correctFalse = tr₁ ⇝t◂ tr₂


open Monoid hiding (refl ; sym ; trans ; setoid ; ε)

module correctLoopTrue {b c s σ s' σ' sb σb sc σc γ γ' n₀}
       (hib : 【 γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ] ++ γ' 】
                  (length γ , σ , s) ⇝*
                  (length (γ ++ b) , σb , suc n₀ ∷ sb))
       (hic : 【 (γ ++ b ++ [ jz (labEnd c) ]) ++ c ++ ([ jmp (labInit b c) ] ++ γ') 】
                  (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb) ⇝*
                  (length ((γ ++ b ++ [ jz (labEnd c) ]) ++ c) , σc , sc))
       (hiloop : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】
                  (length γ , σc , sc) ⇝*
                  (length (γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) , σ' , s')) where


  index₁ : (γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ] ++ γ') ‼
           length (γ ++ b) ≡ just (jz (labEnd c))
  index₁ = propIndex {l₀ = γ} {b} {a = jz (labEnd c)}

  postulate
    p++₁ : ∀ {x} →
         suc (length (γ ++ b)) ≡
         length (γ ++ b ++ [ x ])
  -- p++₁ {x} =
  --   begin
  --     suc (length (γ ++ b))
  --   ≈⟨ len++ (γ ++ b) x ⟩
  --     length ((γ ++ b) ++ [ x ])
  --   ≈⟨ cong length (assoc (monoid Instr) γ b [ x ]) ⟩
  --     length (γ ++ b ++ [ x ])
  --   ∎
  --   where open EqR (setoid ℕ)

  tr₁' : 【 γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ] ++ γ' 】
                  (length γ , σ , s) ⇝*
                  (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb)
  tr₁' = subst
        (λ x → 【 γ ++ b ++ jz (labEnd c) ∷ c ++ jmp (labInit b c) ∷ γ' 】
                length γ , σ , s ⇝* (x , σb , sb)) p++₁ (hib ⇝t◂ (step index₁ ⇝jzs))


  p++₂ : γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ] ++ γ' ≡
         γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ'
  p++₂ = cong (γ ++_) (propAssoc++₅ {l₀ = b} {[ jz (labEnd c) ]} {c})

  tr₁ : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】
                  (length γ , σ , s) ⇝*
                  (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb)
  tr₁ = subst (λ x → 【 x 】
              (length γ , σ , s) ⇝*
              (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb)) p++₂ tr₁'


  tr₂' : 【 (γ ++ b ++ [ jz (labEnd c) ]) ++ c ++ ([ jmp (labInit b c) ] ++ γ') 】
         (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb) ⇝* (length γ , σc , sc)
  tr₂' = subst (λ m → 【 (γ ++ b ++ [ jz (labEnd c) ]) ++ c ++ ([ jmp (labInit b c) ] ++ γ') 】
                        (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb) ⇝* (m , σc , sc))
               p∸
               (hic ⇝t◂ (step (propIndex {l₀ = γ ++ b ++ [ jz (labEnd c) ]}) ⇝jmp))
    where p∸ : length ((γ ++ b ++ [ jz (labEnd c) ]) ++ c) ∸
               (length b + length c + 1) ≡ length γ
          p∸ = prop∸ γ b c (jz (labEnd c))

  tr₂ : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】 
         (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb) ⇝* (length γ , σc , sc)
  tr₂ = subst (λ l →
                 【 l 】 
                 (length (γ ++ b ++ [ jz (labEnd c) ]) , σb , sb) ⇝* (length γ , σc , sc))
              (pAssoc++ {l₀ = γ} {b} {[ jz (labEnd c) ]} {c} {[ jmp (labInit b c) ]}) tr₂'


  correctTrue : 【 γ ++ (b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) ++ γ' 】
                     (length γ , σ , s) ⇝*
                     (length (γ ++ b ++ [ jz (labEnd c) ] ++ c ++ [ jmp (labInit b c) ]) , σ' , s')
  correctTrue = (tr₁ ⇝++ tr₂) ⇝++ hiloop


prop≡× : ∀ {l₀ l₁} {A : Set l₀} {B : Set l₁} → (a a' : A) → (b b' : B) →
           _≡_ {A = A × B} (a , b) (a' , b') →
           a ≡ a' × b ≡ b'
prop≡× a .a b .b refl = refl , refl


ctx-realizes : ∀ {st st'} → DomCₛ st st' → Assm → Set
ctx-realizes f is = ∀ cl s {s'} σ {σ'} →
  f cl (s , σ) ≡ just (s' , σ') → ∀ {γ γ'} → 
  【 γ ++ is ++ γ' 】  (length γ , σ , unty* s) ⇝*
                      (length (γ ++ is) , σ' , unty* s')




{- Generalization of proof correctness -}
postulate
  ctx-prfₛⱼ : ∀ {st st'} {f : DomCₛ st st'} →
                      (lc : LCodeₛ f) → ctx-realizes f (compₗ lc)


-- ctx-prfₛⱼ (pushₙ n) cl s σ refl {γ} {γ'} =
--                     substInstr {γ} (push n) (unty* s) (n ∷ unty* s) σ σ ⇝push
-- ctx-prfₛⱼ add cl (n ▹ (m ▹ s)) σ refl {γ} {γ'} =
--                     substInstr {γ} add (unty* (n ▹ (m ▹ s)))
--                                        (n + m ∷ (unty* s)) σ σ ⇝add
-- ctx-prfₛⱼ eq cl (n ▹ (m ▹ s)) σ refl {γ} {γ'} =
--                     substInstr {γ} eq (unty* (n ▹ (m ▹ s)))
--                                        (unty* ((n ==ₙ m) ▹ s)) σ σ ⇝eq
-- ctx-prfₛⱼ (load x) cl s σ refl {γ} {γ'} =
--                      substInstr {γ} (load x) (unty* s) (σ x ∷ unty* s) σ σ ⇝load
-- ctx-prfₛⱼ (store x) cl (n ▹ s) σ refl {γ} {γ'} =
--                      substInstr {γ} (store x) (unty* (n ▹ s))
--                                     (unty* s) σ (_[_⟶_] σ x n) ⇝store
-- ctx-prfₛⱼ (loop lc lc₁) zero s σ () {γ} {γ'}
-- ctx-prfₛⱼ (loop {st} {fb} {fc} lb lc) (suc cl) s {s'} σ {σ'} p {γ} {γ'}
--                                             with floopInv {cl} {fb = fb} {fc} p
-- ... | inj₁ (sb , σb , fb≡false , sσ'≡sσb) rewrite (proj₁ (prop≡× sb s' σb σ' (sym sσ'≡sσb))) |
--                                                   (proj₂ (prop≡× sb s' σb σ' (sym sσ'≡sσb)))
--                                                   = {!correctFalse!}
--   where hib : _
--         hib = ctx-prfₛⱼ lb (suc cl) s σ fb≡false {γ}
--         open correctLoopFalse {compₗ lb} {compₗ lc} {unty* s} {σ} {unty* s'}
--                                                              {σ'} {γ} {γ'} hib
-- ... | inj₂ (sb , σb , fb≡true , (sc , σc) , fc≡sσc , floop≡sσ') = {!correctTrue!}
--   where hib : _
--         hib = ctx-prfₛⱼ lb (suc cl) s σ fb≡true {γ}
--         hic : _
--         hic = ctx-prfₛⱼ lc (suc cl) sb σb fc≡sσc {γ ++ (compₗ lb) ++ [ jz (labEnd (compₗ lc)) ]}
--         hiloop : _
--         hiloop = ctx-prfₛⱼ (loop lb lc) cl sc σc floop≡sσ' {γ}
--         open correctLoopTrue {compₗ lb} {compₗ lc} {unty* s} {σ} {unty* s'} {σ'}
--                              {unty* sb} {σb} {unty* sc} {σc} {γ} {γ'} hib hic {!hiloop!}

-- ctx-prfₛⱼ (_,c_ {st} {st₀} {st'} {f₀} {f₁} lc₀ lc₁) cl s {s'} σ {σ'} p {γ} {γ'}
--                  with fseqInv {st} {st₀} {st'} {f₀} {f₁} p
-- ... | (s₀ , σ₀) , f₀≡just , f₁≡just =
--          subst (λ c → 【 γ ++ ((compₗ lc₀) ++ (compₗ lc₁)) ++ γ' 】 length γ , σ , unty* s ⇝*
--                        (length c , σ' , unty* s'))
--                (assoc (monoid Instr) γ (compₗ lc₀) (compₗ lc₁))
--                (⇝++subst {γ} {compₗ lc₀} {compₗ lc₁} hi₀ hi₁)
--   where hi₀ : _
--         hi₀ = ctx-prfₛⱼ {st} {st₀} lc₀ cl s σ f₀≡just {γ} {(compₗ lc₁) ++ γ'}
--         hi₁ : _
--         hi₁ = ctx-prfₛⱼ {st₀} {st'} lc₁ cl s₀ σ₀ f₁≡just {γ ++ (compₗ lc₀)} {γ'}
-- ctx-prfₛⱼ (substCₛ lc feq) cl s σ p {γ} {γ'} =
--                    ctx-prfₛⱼ lc cl s σ (trans (feq cl (s , σ)) p) {γ}


realizes : ∀ {st st'} → DomCₛ st st' → Assm → Set
realizes f is = ∀ {cl s s' σ σ'} → f cl (s , σ) ≡ just (s' , σ') →
    【 is 】 (0 , σ , unty* s) ⇝* (length is , σ' , unty* s')


{- Proof of correctness of compilation from Loop language to Jump language -}
prfₛⱼ :  ∀ {st st'} {f : DomCₛ st st'} → (lc : LCodeₛ f) →
            realizes f (compₗ lc)
prfₛⱼ lc {cl} {s} {s'} {σ} {σ'} p =
          subst (λ c₀ → 【 c₀ 】 (0 , σ , unty* s) ⇝* (length (compₗ lc) , σ' , unty* s'))
                (concat[] (compₗ lc))
                (ctx-prfₛⱼ lc cl s σ p {[]} {[]})
  where concat[] : ∀ {A} → (l : List A) → l ++ [] ≡ l
        concat[] [] = refl
        concat[] (x ∷ l) = cong (x ∷_) (concat[] l)


open import While
open import CompWhileLoop


realizesWhile : (p : Stmt) → ⊢ p → Assm → Set
realizesWhile p tp is = ∀ {σ σ' cl} →
          (⟦ p ⇡stmtₜ tp ⟧ₛ cl ∣ σ) ≡ just σ' →
           【 is 】 (0 , σ , []) ⇝* (length is , σ' , [])


compiler :  (p : Stmt) → (tp : ⊢ p) →
               Σ[ c ∈ Assm ] (realizesWhile p tp c)
compiler p tp = (compₗ lcode) , correct
  where
    lcode = compₛ {st = []} (p ⇡stmtₜₛ tp)
    prfₛ : ∀ {σ σ' cl f} → f cl σ ≡ just σ' →
             correctLCodeF f cl (ε , σ) ≡ just (ε , σ')
    prfₛ {f = f} equ rewrite equ = refl
    correct : realizesWhile p tp (compₗ lcode)
    correct equ = prfₛⱼ lcode (prfₛ {f = ⟦ p ⇡stmtₜ tp ⟧ₛ_∣_ } equ)
```