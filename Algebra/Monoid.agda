module NAL.Algebra.Monoid where

open import NAL.Utils.Core
open import NAL.Data.List


record Monoid {ℓ} (M : Set ℓ) : Set ℓ where
  field
    ε : M
    _·_ : M → M → M
    ·-assoc :  {x y z : M} → (x · y) · z ≡ x · (y · z)

mconcat : ∀ {ℓ} {M : Set ℓ} {{_ : Monoid {ℓ} M}} → 𝕃 M → M
mconcat = foldr _·_ ε where open Monoid {{...}}

instance
  listMonoid : ∀ {ℓ} {A : Set ℓ} → Monoid (𝕃 A)
  listMonoid = record {
    ε = [];
    _·_ = _++_ ;
    ·-assoc = λ {x} {y} {z} → sym (++-assoc x y z)}
