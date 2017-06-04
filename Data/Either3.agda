module NAL.Data.Either3 where

open import NAL.Utils.Core

data Either3 {ℓ₁ ℓ₂ ℓ₃} (A : Set ℓ₁) (B : Set ℓ₂) (C : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  Left : A → Either3 A B C
  Middle : B → Either3 A B C
  Right : C → Either3 A B C

