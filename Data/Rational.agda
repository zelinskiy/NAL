module NAL.Data.Rational where

import NAL.Data.Nats as ℕ
open import NAL.Data.Integer renaming (_≤_ to _|≤|_; _==_ to _|==|_;  _<_ to _|<|_;  _-_ to _|-|_; _*_ to _|*|_; _+_ to _|+|_; abs to |abs|)
open import NAL.Data.Bool

infix 80 _*_ _÷_
infix 60 _-_ _+_ 
infix 100 _/_

record ℚ : Set where
  constructor _/_
  field
    p : ℤ
    q : ℤ

open ℚ

ℚ0 : ℚ
ℚ0 = ℤ0 / mkℤ 1

mkℚ : ℤ → ℚ
mkℚ z = z / mkℤ 1


_≤_ : ℚ → ℚ → 𝔹
a / b ≤ c / d = a |*| d |≤| b |*| c

_==_ : ℚ → ℚ → 𝔹
a == b = a ≤ b ∧ b ≤ a

_<_ : ℚ → ℚ → 𝔹
a < b = if a == b then ff else (a ≤ b)

_-_ : ℚ → ℚ → ℚ
a / b - c / d = (a |*| d |-| b |*| c) / (b |*| d)

_+_ : ℚ → ℚ → ℚ
a / b + c / d = (a |*| d |+| b |*| c) / (b |*| d)

_÷_ : ℚ → ℚ → ℚ
a / b ÷ c / d = (a |*| d) / (b |*| c)

_*_ : ℚ → ℚ → ℚ
a / b * c / d = (a |*| b) / (c |*| d)

abs : ℚ → ℚ
abs (a / b) = (|abs| a) / b
