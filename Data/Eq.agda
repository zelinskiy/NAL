module NAL.Data.Eq where

open import NAL.Data.Bool
open import NAL.Data.Nats


record Eq {ℓ}(A : Set ℓ) : Set ℓ where
  field
    _is_ : A → A → 𝔹

open Eq {{...}} public

instance
  Eqℕ : Eq ℕ
  Eqℕ = record { _is_ = h }
    where
      h : ℕ → ℕ → 𝔹
      h 0 0 = tt
      h (suc x) (suc y) = h x y
      h _ _ = ff

instance
  Eq𝔹 : Eq 𝔹
  Eq𝔹 = record {_is_ = h}
    where
      h : 𝔹 → 𝔹 → 𝔹
      h tt tt = tt
      h ff ff = tt
      h _  _  = ff

