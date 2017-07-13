module NAL.Data.Vector where

open import NAL.Data.Fin
open import NAL.Data.Nats
open import NAL.Data.Bool

open import NAL.Utils.Core

infixr 40 _::_

data 𝕍 {ℓ} (A : Set ℓ) : (n : ℕ) → Set ℓ where
  [] : 𝕍 A 0
  _::_ : ∀ {n} (x : A) (xs : 𝕍 A n) → 𝕍 A (suc n)

_!_ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → (xs : 𝕍 A n) → (m : Fin n) → A
_!_ (x :: xs) zero = x
_!_ (x :: xs) (suc m) = _!_ xs m
