module NAL.Examples.LCHI.Part7 where

open import NAL.Data.List
open import NAL.Data.Pair

open import NAL.Utils.Core renaming (⊥ to Bot; ⊤ to Top)

open import NAL.Examples.LCHI.Part2 using (Φ; Context; _[_:=_])

open Φ

data _⊢_ : Context → Φ → Set where

  -- | Identity rules (Axiom) |  
  Ax : ∀ {φ Γ} → φ :: Γ ⊢ φ
  
  -- | Logical rules |  
  L∧₁ : ∀{Γ σ φ ψ} → φ :: Γ ⊢ σ → (φ ∧ ψ) :: Γ ⊢ σ
  L∧₂ : ∀{Γ σ φ ψ} → ψ :: Γ ⊢ σ → (φ ∧ ψ) :: Γ ⊢ σ
  R∧ : ∀{Γ φ ψ} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ (φ ∧ ψ)
  
  L∨ : ∀{Γ σ φ ψ} → φ :: Γ ⊢ σ → ψ :: Γ ⊢ σ → (φ ∨ ψ) :: Γ ⊢ σ
  R∧₁ : ∀{Γ φ ψ} → Γ ⊢ φ → Γ ⊢ (φ ∧ ψ)
  R∧₂ : ∀{Γ φ ψ} → Γ ⊢ ψ → Γ ⊢ (φ ∧ ψ)

  L⊃ : ∀{Γ σ φ ψ} → Γ ⊢ φ → ψ :: Γ ⊢ σ → (φ ⊃ ψ) :: Γ ⊢ σ
  R⊃ : ∀{Γ φ ψ} → φ :: Γ ⊢ ψ → Γ ⊢ (φ ⊃ ψ)

  L⊥ : ∀{Γ σ} → ⊥ :: Γ ⊢ σ

  -- | Structural rules |
  Cut : ∀{Γ σ φ} → Γ ⊢ φ → φ :: Γ ⊢ σ → Γ ⊢ σ  
  Ex : ∀{Γ φ n} → Γ ⊢ φ → exchange n Γ ⊢ φ  
  Contr : ∀{Γ σ φ} → φ :: φ :: Γ ⊢ σ → φ :: Γ ⊢ σ  
  Weak : ∀{Γ σ φ} → Γ ⊢ σ → φ :: Γ ⊢ σ

cutFree : ∀ {Γ φ} → Γ ⊢ φ → Set
cutFree (Cut p q) = Bot
cutFree Ax = Top
cutFree (L∧₁ p) = cutFree p
cutFree (L∧₂ p) = cutFree p
cutFree (R∧ p q) = ⟪ cutFree p , cutFree q ⟫
cutFree (L∨ p q) = ⟪ cutFree p , cutFree q ⟫
cutFree (R∧₁ p) = cutFree p
cutFree (R∧₂ p) = cutFree p
cutFree (L⊃ p q) = ⟪ cutFree p , cutFree q ⟫
cutFree (R⊃ p) = cutFree p
cutFree L⊥ = Top
cutFree (Ex p) = cutFree p
cutFree (Contr p) = cutFree p
cutFree (Weak p) = cutFree p

Not : Set → Set
Not a = a → Bot

postulate HauptSatz : ∀ {Γ φ} {p : Γ ⊢ φ} → Not (cutFree p) → cutFree p
