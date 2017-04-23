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

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc ℤ y z = refl
+assoc (𝕊 x) y z rewrite +assoc x y z = refl

==trans : ∀ (x y z : ℕ) → (x == y) ≡ tt → (y == z) ≡ tt → (x == z) ≡ tt
==trans ℤ ℤ ℤ p q = refl
==trans (𝕊 _) ℤ _ ()
==trans (𝕊 _) (𝕊 _) ℤ p ()
==trans ℤ (𝕊 _) _ ()
==trans ℤ ℤ (𝕊 _) p ()
==trans (𝕊 x) (𝕊 y) (𝕊 z) p q rewrite ==trans x y z p q = refl

==comm : ∀ (x y : ℕ) → x == y ≡ y == x
==comm ℤ ℤ = refl
==comm ℤ (𝕊 y) = refl
==comm (𝕊 x) ℤ = refl
==comm (𝕊 x) (𝕊 y) rewrite ==comm x y = refl
