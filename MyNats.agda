module MyNats where

open import Agda.Builtin.Equality
open import MyBool

data ℕ : Set where
  ℤ : ℕ
  𝕊 : ℕ → ℕ

{-# BUILTIN NATURAL  ℕ  #-}


_==_ : ℕ → ℕ → 𝔹
ℤ == ℤ = tt
𝕊 x == 𝕊 y = x == y
_==_ _ _ = ff

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

==refl : ∀ (x : ℕ) → x == x ≡ tt
==refl ℤ = refl
==refl (𝕊 x) rewrite ==refl x = refl

_+_ : ℕ → ℕ → ℕ
ℤ + n = n
𝕊 m + n = 𝕊 (m + n)

infixl 25 _+_

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 ℤ = refl
+0 (𝕊 x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc ℤ y z = refl
+assoc (𝕊 x) y z rewrite +assoc x y z = refl

+suc-lemma : ∀ (x y : ℕ) → x + (𝕊 y) ≡ 𝕊 (x + y)
+suc-lemma ℤ y = refl
+suc-lemma (𝕊 x) y rewrite +suc-lemma x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm ℤ y rewrite +0 y = refl
+comm (𝕊 x) y  rewrite +comm x y | +suc-lemma y x = refl

_*_ : ℕ → ℕ → ℕ
ℤ * n = ℤ
𝕊 a * b = b + (a * b)

infixl 30 _*_ 

*rdistr+ : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*rdistr+ ℤ y z = refl
*rdistr+ (𝕊 x) y z rewrite *rdistr+ x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * ℤ ≡ ℤ
*0 ℤ = refl
*0 (𝕊 x) rewrite *0 x = refl

*1 : ∀ (x : ℕ) → x * 𝕊 ℤ ≡ x
*1 ℤ = refl
*1 (𝕊 x) rewrite *1 x = refl


*suc-lemma : ∀ (x y : ℕ) → x * (𝕊 y) ≡ x + x * y
*suc-lemma ℤ y = refl
*suc-lemma (𝕊 x) y rewrite *suc-lemma x y | +assoc y x (x * y) | +assoc x y (x * y) | +comm y x  = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm ℤ y rewrite *0 y = refl
*comm (𝕊 x) y rewrite  *suc-lemma y x | *comm x y = refl

*assoc : ∀ (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*assoc ℤ y z  = refl
*assoc (𝕊 x) y z rewrite *assoc x y z | *rdistr+ y (x * y) z | *assoc x y z = refl


_<_ : ℕ → ℕ → 𝔹
ℤ < ℤ = ff
ℤ < 𝕊 y = tt
𝕊 x < ℤ = ff
𝕊 x < 𝕊 y = x < y

<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 ℤ = refl
<-0 (𝕊 x) rewrite <-0 x = refl


<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {x} {ℤ} p q rewrite <-0 x = 𝔹-contra p
<-trans {ℤ} {𝕊 y} {ℤ} p ()
<-trans {ℤ} {𝕊 y} {𝕊 z} p q = refl
<-trans {𝕊 x} {𝕊 y} {ℤ} p ()
<-trans {𝕊 x} {𝕊 y} {𝕊 z} p q = <-trans {x} {y} {z} p q

