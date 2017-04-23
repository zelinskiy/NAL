module MyNats where

open import Agda.Builtin.Equality
open import MyBool

data ℕ : Set where
  ℤ : ℕ
  𝕊 : ℕ → ℕ

{-# BUILTIN NATURAL  ℕ  #-}

_+_ : ℕ → ℕ → ℕ
ℤ + n = n
𝕊 m + n = 𝕊 (m + n)

_==_ : ℕ → ℕ → 𝔹
ℤ == ℤ = tt
𝕊 x == 𝕊 y = x == y
_==_ _ _ = ff

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 ℤ = refl
+0 (𝕊 x) rewrite +0 x = refl
