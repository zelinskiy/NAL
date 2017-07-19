module NAL.Examples.LCHI.Part7-classical where

open import NAL.Data.List

open import NAL.Examples.LCHI.Part2 using (Φ; Context; _[_:=_])

open Φ

data _⊢_ : Context → Context → Set where

  -- | Identity rules (Axiom) |  
  Ax : ∀ {φ Γ Δ} → φ :: Γ ⊢ φ :: Δ
  
  -- | Logical rules |  
  L∧₁ : ∀{Γ Δ φ ψ} → φ :: Γ ⊢ Δ → (φ ∧ ψ) :: Γ ⊢ Δ
  L∧₂ : ∀{Γ Δ φ ψ} → ψ :: Γ ⊢ Δ → (φ ∧ ψ) :: Γ ⊢ Δ
  R∧ : ∀{Γ Δ φ ψ} → Γ ⊢ φ :: Δ → Γ ⊢ ψ :: Δ → Γ ⊢ (φ ∧ ψ) :: Δ
  
  L∨ : ∀{Γ Δ φ ψ} → φ :: Γ ⊢ Δ → ψ :: Γ ⊢ Δ → (φ ∨ ψ) :: Γ ⊢ Δ
  R∧₁ : ∀{Γ Δ φ ψ} → Γ ⊢ φ :: Δ → Γ ⊢ (φ ∧ ψ) :: Δ
  R∧₂ : ∀{Γ Δ φ ψ} → Γ ⊢ ψ :: Δ → Γ ⊢ (φ ∧ ψ) :: Δ

  L⊃ : ∀{Γ Δ Θ φ ψ} → Γ ⊢ φ :: Δ → ψ :: Γ ⊢ Θ → (φ ⊃ ψ) :: Γ ⊢ Δ ++ Θ
  R⊃ : ∀{Γ Δ φ ψ} → φ :: Γ ⊢ ψ :: Δ → Γ ⊢ (φ ⊃ ψ) :: Δ

  L⊥ : ∀{Γ Δ} → ⊥ :: Γ ⊢ Δ

  -- | Structural rules |
  Cut : ∀{Γ Δ Θ φ} → Γ ⊢ φ :: Δ → φ :: Δ ⊢ Θ → Γ ⊢ Δ ++ Θ
  
  LEx : ∀{Γ Δ n} → Γ ⊢ Δ → exchange n Γ ⊢ Δ
  REx : ∀{Γ Δ n} → Γ ⊢ Δ → Γ ⊢ exchange n Δ
    
  LC : ∀{Γ Δ φ} → φ :: φ :: Γ ⊢ Δ → φ :: Γ ⊢ Δ
  RC : ∀{Γ Δ φ} → Γ ⊢ φ :: φ :: Δ → Γ ⊢ φ :: Δ
  
  LW : ∀{Γ Δ φ} → Γ ⊢ Δ → φ :: Γ ⊢ Δ
  RW : ∀{Γ Δ φ} → Γ ⊢ Δ → Γ ⊢ φ :: Δ
