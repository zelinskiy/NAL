module MyMonoid where

open import Agda.Primitive
open import Utils
open import MyList


record Monoid {ℓ} (M : Set ℓ) : Set ℓ where
  field
    ε : M
    _·_ : M → M → M
    ·-assoc :  {x y z : M} → (x · y) · z ≡ x · (y · z)

instance
  listMonoid : ∀ {ℓ} {A : Set ℓ} → Monoid (𝕃 A)
  listMonoid = record {
    ε = [];
    _·_ = _++_ ;
    ·-assoc = λ {x} {y} {z} → sym (++-assoc x y z)}
