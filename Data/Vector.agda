module NAL.Data.Vector where

open import NAL.Data.Nats

data 𝕍 {ℓ} (A : Set ℓ) : (n : ℕ) → Set ℓ where
  [] : 𝕍 A 0
  _::_ : ∀ {n} (x : A) (xs : 𝕍 A n) → 𝕍 A (suc n)
