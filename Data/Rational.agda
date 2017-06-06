module NAL.Data.Rational where

import NAL.Data.Nats as ℕ
import NAL.Data.Integer as ℤ
open import NAL.Data.Bool

open ℕ using (ℕ)
open ℤ using (ℤ; ℤ0; mkℤ)

infix 100 _/_

record ℚ : Set where
  constructor _/_
  field
    p : ℤ
    q : ℕ

open ℚ

ℚ0 : ℚ
ℚ0 = ℤ0 / 1

 
_≤_ : ℚ → ℚ → 𝔹
a ≤ b = ((p a) ℤ.* (mkℤ (q b))) ℤ.≤ ((mkℤ (q a))  ℤ.* (p b))

_==_ : ℚ → ℚ → 𝔹
a == b = a ≤ b ∧ b ≤ a

_<_ : ℚ → ℚ → 𝔹
a < b = if (a == b) then ff else (a ≤ b)

_-_ : ℚ → ℚ → ℚ
a / b - c / d = ((a ℤ.* mkℤ d) ℤ.- (mkℤ b ℤ.* c)) / (b ℕ.* d)

abs : ℚ → ℚ
abs (a / b) = (ℤ.abs a) / b
