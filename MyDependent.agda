module MyDependent where

open import Level using (_⊔_)

record Σ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor Σ_,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public
