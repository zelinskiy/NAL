module NAL.Data.Maybe where

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  Nothing : Maybe A
  Just : A → Maybe A

open Maybe public
