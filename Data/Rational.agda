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

open import NAL.Utils.Core
open import NAL.Utils.Dependent

postulate
  0/n : (n : ℤ) → ℤ0 / n ≡ ℚ0
  n/0 : (n : ℤ) → Σ ℚ (λ q → n / ℤ0 ≡ q) → ⊥
  n/-m : {m : ℕ.ℕ} → (n : ℤ) → n / Int (ℕ.suc m) ff ≡ neg n / Int (ℕ.suc m) tt
  TriangleProp : (a b : ℚ) → abs (a + b) ≤ (abs a) + (abs b) ≡ tt



{-
+ℚ0 : (n : ℚ) → n + ℚ0 ≡ n
+ℚ0 (Int ℕ.zero ⊤-intro / Int ℕ.zero ⊤-intro) = refl
+ℚ0 (Int ℕ.zero ⊤-intro / Int (ℕ.suc m) tt) rewrite 0/n (Int (ℕ.suc m) tt) | 0/n (Int (ℕ.suc (m ℕ.* 1)) tt) = refl
+ℚ0 (Int ℕ.zero ⊤-intro / Int (ℕ.suc m) ff) rewrite 0/n (Int (ℕ.suc m) ff) = {!!}
+ℚ0 (Int (ℕ.suc n) tt / Int ℕ.zero ⊤-intro) = ⊥-elim (n/0 (Int (ℕ.suc n) tt) (Σ Int (ℕ.suc n) tt / ℤ0 , refl))
+ℚ0 (Int (ℕ.suc n) tt / Int (ℕ.suc m) tt) = {!!}
+ℚ0 (Int (ℕ.suc n) tt / Int (ℕ.suc m) ff) = {!!}
+ℚ0 (Int (ℕ.suc n) ff / Int ℕ.zero ⊤-intro) = ⊥-elim (n/0 (Int (ℕ.suc n) ff) (Σ Int (ℕ.suc n) ff / ℤ0 , refl))
+ℚ0 (Int (ℕ.suc n) ff / Int (ℕ.suc m) tt) = {!!}
+ℚ0 (Int (ℕ.suc n) ff / Int (ℕ.suc m) ff) = {!!}
-}

{-

WiggleLemma : (r s ε : ℚ) → ℚ0 < ε ≡ tt → r ≤ s + ε ≡ tt → r ≤ s ≡ tt
WiggleLemma r s (Int ℕ.zero ⊤-intro / Int ℕ.zero ⊤-intro) p q = {!!}
WiggleLemma r s (Int ℕ.zero ⊤-intro / Int (ℕ.suc m) tt) p q = {!!}
WiggleLemma r s (Int ℕ.zero ⊤-intro / Int (ℕ.suc m) ff) p q = {!!}
WiggleLemma r s (Int (ℕ.suc n) tt / Int ℕ.zero ⊤-intro) p q = {!!}
WiggleLemma r s (Int (ℕ.suc n) tt / Int (ℕ.suc m) tt) p q = {!!}
WiggleLemma r s (Int (ℕ.suc n) tt / Int (ℕ.suc m) ff) p q = {!!}
WiggleLemma r s (Int (ℕ.suc n) ff / Int ℕ.zero ⊤-intro) p q = {!!}
WiggleLemma r s (Int (ℕ.suc n) ff / Int (ℕ.suc m) tt) p q = {!!}
WiggleLemma r s (Int (ℕ.suc n) ff / Int (ℕ.suc m) ff) p q = {!!}
-}
