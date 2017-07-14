module NAL.Examples.Peano where

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL  ℕ  #-}

infix 4 _≅_

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
   refl : x ≅ x

data ⊥ : Set where

¬_ : Set → Set
¬ x = x → ⊥

cong : {A B : Set}{a b : A}{f : A → B} →
  a ≅ b → f a ≅ f b
cong refl = refl

data _∧_  (A : Set) (B : Set) : Set where
  _,_ : A → B → A ∧ B

_⟷_ : Set → Set → Set
a ⟷ b = (a → b) ∧ (b → a)

linj : {m n : ℕ} → S m ≅ S n → m ≅ n
linj refl = refl

rinj : {m n : ℕ} → m ≅ n → S m ≅ S n
rinj refl = refl

-------------------------------------------------------------------------------------------------------------

Ax1 : ℕ
Ax1 = 0

Ax2 : (x : ℕ) → x ≅ x
Ax2 x = refl

Ax3 : (x y : ℕ) → x ≅ y → y ≅ x
Ax3 Z Z p = refl
Ax3 Z (S y) ()
Ax3 (S x) Z ()
Ax3 (S x) (S y) p = cong (Ax3 x y (linj p))

Ax4 : {x y z : ℕ} → x ≅ y → y ≅ z → x ≅ z
Ax4 refl refl = refl

Ax5 : {B : Set}{a : ℕ}{b : B} →  a ≅ b → B ≅ ℕ
Ax5 refl = refl

Ax6 : {A B : Set}{m : B}{n : A} → A ≅ ℕ → n ≅ m → B ≅ ℕ
Ax6 refl refl = refl

Ax7 : (x y : ℕ) → (x ≅ y) ⟷ (S x ≅ S y)
Ax7 a b = rinj , linj

Ax8 : {n : ℕ} → ¬ (S n ≅ 0)
Ax8 ()

Ax9 : (φ : ℕ → Set) → φ 0 → ((x : ℕ) → φ x → φ (S x)) → (n : ℕ) → φ n
Ax9 φ p q 0 = p
Ax9 φ p q (S n) = q n (Ax9 φ p q n)

