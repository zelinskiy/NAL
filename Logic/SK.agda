module NAL.Logic.SK where

open import NAL.Utils.Core
open import NAL.Data.Nats

data ↓ {ℓ₁ ℓ₂} {A : Set ℓ₁}
  (_>_ : A → A → Set ℓ₂) :
  A → Set (ℓ₁ ⊔ ℓ₂)
  where
  pf↓ : ∀ {x : A} →
          (∀ {y : A} → x > y → ↓ _>_ y) →
          ↓ _>_ x

-- Example : Termination of _>_ on ℕ
module Example where
  open import NAL.Data.Bool
  open import NAL.Data.Nats
  open import NAL.Data.Either
  
  ↓𝔹 : ∀ {ℓ} {A : Set ℓ} (_>_ : A → A → 𝔹) → A → Set ℓ
  ↓𝔹 {ℓ} {A} _>_ x = ↓ {ℓ} {lzero} (λ (x y : A) → (x > y) ≡ tt) x

  <-drop : ∀ {x y : ℕ} → (x < (suc y) ≡ tt) → Either (x ≡ y) (x < y ≡ tt)
  <-drop {zero} {zero} p = Left refl
  <-drop {zero} {suc y} p = Right refl
  <-drop {suc x} {zero} p rewrite <-0 x = 𝔹-contra p
  <-drop {suc x} {suc y} p with <-drop {x} {y} p
  ...                                     | Left a = Left (cong a)
  ...                                     | Right a = Right a
  
  
  ↓-> : ∀ (n : ℕ) → ↓𝔹 _>_ n
  ↓-> n = pf↓ (h n)
    where
      h : ∀ x → ∀ {y} → x > y ≡ tt → ↓𝔹 _>_ y
      h 0 {0} ()
      h 0 {suc _} ()
      h (suc x) {y} p with <-drop {y} p
      ... | Left q rewrite q = ↓-> x
      ... | Right q = h x q

--monotonicity?
module Measure {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
                           {A : Set ℓ₁}
                           {B : Set ℓ₂}
                           (_>A_ : A → A → Set ℓ₃)
                           (_>B_ : B → B → Set ℓ₄)
                           (m : A → B)
                           (dm : ∀ {a₁ a₂ : A} → a₁ >A a₂ → m a₁ >B m a₂)
                           
  where

  measure-↓ : ∀ {a : A} → ↓ _>B_ (m a) → ↓ _>A_ a
  measure-↓ {a} (pf↓ fM) = pf↓ h
    where
      h : {y : A} → a >A y → ↓ _>A_ y
      h {y} p = measure-↓ (fM (dm p))
  

infixl 80 _$_

data Comb : Set where
  S : Comb
  K : Comb
  _$_ : Comb → Comb → Comb


size : Comb → ℕ
size S = 1
size K = 1
size (a $ b) = suc (size a + size b)

data _↠_ : Comb → Comb → Set where
  ↠K : (a b : Comb) → ((K $ a) $ b) ↠ a
  ↠S : (a b c : Comb) → (((S $ a) $ b) $ c) ↠ (a $ c) $ (b $ c)
  ↠CongL : {a b : Comb} (c : Comb) → a ↠ b → (c $ a) ↠ (c $ b)
  ↠CongR : {a b : Comb} (c : Comb) → a ↠ b → (a $ c) ↠ (b $ c)
