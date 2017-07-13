module NAL.Examples.LCHI.Part4 where

open import NAL.Data.List
open import NAL.Data.String
open import NAL.Data.Nats

open import NAL.Utils.Core renaming (⊥ to Absurd)
open import NAL.Utils.Function
open import NAL.Utils.Dependent hiding (Π)

import NAL.Examples.LCHI.Part2 as Part2
open import NAL.Examples.LCHI.Part3 renaming (_∷_ to _of_)

open Part2.IPC renaming (var' to var; _⊃'_ to _⊃_; _⊢'_ to _⊢_;
  Ax' to Ax; ⊃I' to ⊃I; ⊃E' to ⊃E; IPC to Φ)

fromΠ : Π → Φ
fromΠ (tvar x) = var x
fromΠ (φ ⇒ ψ) = (fromΠ φ) ⊃ (fromΠ ψ)

toΠ : Φ → Π
toΠ (var x) = tvar x
toΠ (φ ⊃ ψ) = (toΠ φ) ⇒ (toΠ ψ)

fromToΠ : ∀{φ} → fromΠ (toΠ φ) ≡ φ
fromToΠ {var x} = refl
fromToΠ {φ ⊃ ψ} rewrite fromToΠ {φ} | fromToΠ {ψ} = refl

toFromΠ : ∀{φ} → toΠ (fromΠ φ) ≡ φ
toFromΠ {tvar x} = refl
toFromΠ {φ ⇒ ψ} rewrite toFromΠ {φ} | toFromΠ {ψ} = refl

∣_∣ : 𝕃 Binding → 𝕃 Φ
∣_∣ = map fromΠ ∘ ran

CurryHoward1 : ∀{Γ M φ} → Γ ⊢ M ∷ φ → ∣ Γ ∣ ⊢ fromΠ φ
CurryHoward1 Ax = Ax
CurryHoward1 (Abs p) = ⊃I (CurryHoward1 p)
CurryHoward1 (App M N) = ⊃E (CurryHoward1 M) (CurryHoward1 N)

showΦ : Φ → String
showΦ (var x) = x
showΦ (φ ⊃ ψ) = primStringAppend (primStringAppend (showΦ ψ) " -> ") (showΦ ψ)

mkΔ : 𝕃 Φ → 𝕃 Binding
mkΔ [] = []
mkΔ  (φ :: φs) = (y of toΠ φ) :: mkΔ φs where y = primStringAppend "x_" (showΦ φ)

CurryHoward2 : ∀ {Γ φ} → Γ ⊢ φ → Σ Λ (λ M → mkΔ Γ ⊢ M ∷ toΠ φ) 
CurryHoward2 Ax = Σ _ , Ax
CurryHoward2 (⊃I {φ = φ} p) = Σ (ƛ x ! π₁ p') , Abs (π₂ p')
  where
    p'  = CurryHoward2 p
    x = primStringAppend "x_" (showΦ φ)
CurryHoward2 (⊃E p q) = Σ π₁ p' $ π₁ q' , App (π₂ p') (π₂ q')
  where
    p' = CurryHoward2 p
    q' = CurryHoward2 q
 

lemma1 :  ∀ {Γ φ} → Γ ⊢ fromΠ (toΠ φ) → Γ ⊢ φ
lemma1 {Γ} {φ} p rewrite fromToΠ {φ} = p

{-
IDEA :
Take proof
Make typed lambda term from it
Normalize term
Make (normalized) proof from (normalized) term
-}

nbe : ∀ {Γ φ} → Γ ⊢ φ →  ∣ mkΔ Γ ∣ ⊢ φ
nbe {Γ} {φ} proof rewrite  sym (fromToΠ {φ}) = normProof  
  where
    ch2 = CurryHoward2 {Γ} {φ} (lemma1 {Γ} {φ} proof)
    term = π₁ ch2
    red = normTyped (π₂ ch2)
    red' = π₁ red
    red2 = SubjectReduction2 {M = term} {N = red'} (π₂ ch2) (normIsBeta (π₂ red))
    normProof = CurryHoward1 {mkΔ Γ} {red'} {toΠ φ}  red2


{-
IPCconsistent : [] ⊢ var "_|_" → Absurd
IPCconsistent (⊃E {φ = φ} p q) = {!!}
  where
    pλ = CurryHoward2 p
    qλ = CurryHoward2 q
-}
