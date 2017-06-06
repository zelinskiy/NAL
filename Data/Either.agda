module NAL.Data.Either where

open import NAL.Utils.Core

data Either {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  Left : A → Either A B
  Right : B → Either A B


infixr 1 _⊎_
_⊎_ : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
_⊎_ = Either
