module NAL.Data.Maybe where

open import NAL.Data.Bool

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  Nothing : Maybe A
  Just : A → Maybe A

isJust : ∀{ℓ} {A : Set ℓ} → Maybe A → 𝔹
isJust (Just _) = tt
isJust Nothing = ff

open Maybe public
