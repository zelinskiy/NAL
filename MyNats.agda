module MyNats where


open import Utils
open import MyBool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL  ℕ  #-}







_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 25 _+_


2+2 : 2 + 2 ≡ 4
2+2 = refl

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc-lemma : ∀ (x y : ℕ) → x + (suc y) ≡ suc (x + y)
+suc-lemma zero y = refl
+suc-lemma (suc x) y rewrite +suc-lemma x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y  rewrite +comm x y | +suc-lemma y x = refl








_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc a * b = b + (a * b)

infixl 30 _*_ 

*rdistr+ : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*rdistr+ zero y z = refl
*rdistr+ (suc x) y z rewrite *rdistr+ x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * zero ≡ zero
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*1 : ∀ (x : ℕ) → x * suc zero ≡ x
*1 zero = refl
*1 (suc x) rewrite *1 x = refl


*suc-lemma : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc-lemma zero y = refl
*suc-lemma (suc x) y rewrite *suc-lemma x y | +assoc y x (x * y) | +assoc x y (x * y) | +comm y x  = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite  *suc-lemma y x | *comm x y = refl

*assoc : ∀ (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
*assoc zero y z  = refl
*assoc (suc x) y z rewrite *assoc x y z | *rdistr+ y (x * y) z | *assoc x y z = refl

*ldistr+ : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*ldistr+ x zero z rewrite *comm x (zero + z) | *0 x   = refl
*ldistr+ x (suc y) z rewrite *suc-lemma x (y + z) | *suc-lemma x y | *ldistr+ x y z | +assoc x (x * y) (x * z)= refl






_<_ : ℕ → ℕ → 𝔹
zero < zero = ff
zero < suc y = tt
suc x < zero = ff
suc x < suc y = x < y


<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 zero = refl
<-0 (suc x) rewrite <-0 x = refl


<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {x} {zero} p q rewrite <-0 x = 𝔹-contra p
<-trans {zero} {suc y} {zero} p ()
<-trans {zero} {suc y} {suc z} p q = refl
<-trans {suc x} {suc y} {zero} p ()
<-trans {suc x} {suc y} {suc z} p q = <-trans {x} {y} {z} p q

<-suc : ∀ (n : ℕ) → n < suc n ≡ tt
<-suc 0 = refl
<-suc (suc n) rewrite <-suc n = refl

_≤_ : ℕ → ℕ → 𝔹
zero ≤ zero = tt
zero ≤ suc y = tt
suc x ≤ zero = ff
suc x ≤ suc y = x ≤ y

≤-0 : ∀ {x : ℕ} → (x ≤ zero) ≡ tt → x ≡ zero
≤-0 {zero} p = refl
≤-0 {suc x} ()

≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ tt → y ≤ z ≡ tt → x ≤ z ≡ tt
≤-trans {zero} {zero} {zero} p q = refl
≤-trans {zero} {zero} {suc z} p q = refl
≤-trans {zero} {suc y} {zero} p q = refl
≤-trans {zero} {suc y} {suc z} p q = refl
≤-trans {suc x} {zero} {zero} ()
≤-trans {x} {zero} {suc z} p q  rewrite ≤-0 {x} p = refl
≤-trans {suc x} {suc y} {zero} p ()
≤-trans {suc x} {suc y} {suc z} p q = ≤-trans {x} {y} {z} p q


≤-refl : ∀ (x : ℕ) → x ≤ x ≡ tt
≤-refl zero = refl
≤-refl (suc x) rewrite ≤-refl x = refl

≤-suc : ∀ (n : ℕ) → n ≤ suc n ≡ tt
≤-suc zero = refl
≤-suc (suc n) rewrite ≤-suc n = refl


_==_ : ℕ → ℕ → 𝔹
zero == zero = tt
suc x == suc y = x == y
_==_ _ _ = ff

==trans : ∀ (x y z : ℕ) → (x == y) ≡ tt → (y == z) ≡ tt → (x == z) ≡ tt
==trans zero zero zero p q = refl
==trans (suc _) zero _ ()
==trans (suc _) (suc _) zero p ()
==trans zero (suc _) _ ()
==trans zero zero (suc _) p ()
==trans (suc x) (suc y) (suc z) p q rewrite ==trans x y z p q = refl

==comm : ∀ (x y : ℕ) → x == y ≡ y == x
==comm zero zero = refl
==comm zero (suc y) = refl
==comm (suc x) zero = refl
==comm (suc x) (suc y) rewrite ==comm x y = refl

==refl : ∀ (x : ℕ) → x == x ≡ tt
==refl zero = refl
==refl (suc x) rewrite ==refl x = refl


==-to-≡ : ∀ {x y : ℕ} → x == y ≡ tt → x ≡ y
==-to-≡ {zero} {zero} p = refl
==-to-≡ {zero} {suc y} ()
==-to-≡ {suc x} {zero} () 
==-to-≡ {suc x} {suc y} p rewrite ==-to-≡ {x} {y} p = refl


≡-to-== : ∀ {x y : ℕ} → x ≡ y → x == y ≡ tt
≡-to-== {x} refl = ==refl x

f : (n : ℕ) → ℕ
f zero = suc zero
f (suc x) = (suc x) * (f x)


≤-antisymm : ∀ (x y : ℕ) → x ≤ y ≡ tt → y ≤ x ≡ tt → y == x ≡ tt
≤-antisymm zero zero p q = refl
≤-antisymm zero (suc y)  p ()
≤-antisymm (suc x) zero ()
≤-antisymm (suc x) (suc y) p q rewrite ≤-antisymm x y p q = refl

subtract : (x y : ℕ) (p : y ≤ x ≡ tt) → ℕ
subtract x zero p = x
subtract zero (suc y) ()
subtract (suc x) (suc y) p = subtract x y p
