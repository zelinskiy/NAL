module NAL.Data.Bool where

open import NAL.Utils.Core

data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

{-# BUILTIN BOOL 𝔹 #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}


infix 7 ¬_

¬_ : 𝔹 → 𝔹
¬ tt = ff
¬ ff = tt

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then a₁ else a₂ = a₁
if ff then a₁ else a₂ = a₂

infixl 5 _∧_

_∧_ : 𝔹 → 𝔹 → 𝔹
tt ∧ tt = tt
a  ∧ b  = ff

infixl 4 _∨_

_∨_ : 𝔹 → 𝔹 → 𝔹
tt ∨ b = tt
ff ∨ b = b

infixl 5 _xor_

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor ff  = tt
ff  xor tt = tt
a  xor b  = ff

xor-comm : ∀{x y r} → x xor y ≡ r → y xor x ≡ r
xor-comm {tt} {tt} {tt} p = p
xor-comm {tt} {tt} {ff} p = p
xor-comm {tt} {ff} {tt} p = refl
xor-comm {tt} {ff} {ff} p = p
xor-comm {ff} {tt} {tt} p = refl
xor-comm {ff} {tt} {ff} p = p
xor-comm {ff} {ff} {tt} p = p
xor-comm {ff} {ff} {ff} p = refl

xor-ff-equal : ∀{x y} → x xor y ≡ ff → x ≡ y
xor-ff-equal {tt} {tt} p = refl
xor-ff-equal {tt} {ff} ()
xor-ff-equal {ff} {tt} ()
xor-ff-equal {ff} {ff} p = refl

infixl 5 _equiv_

_equiv_ : 𝔹 → 𝔹 → 𝔹
tt equiv tt  = tt
ff equiv ff = tt
a  equiv b  = ff

infixl 5 _implies_

_implies_ : 𝔹 → 𝔹 → 𝔹
tt implies ff = ff
_ implies _ = tt



¬¬-elim : ∀ (x : 𝔹) → ¬ ¬ x ≡ x
¬¬-elim tt = refl
¬¬-elim ff = refl

∧-refl : ∀ (x : 𝔹) → x ∧ x ≡ x
∧-refl tt = refl
∧-refl ff = refl

∧-elim₁ : ∀ {x y} → x ∧ y ≡ tt → x ≡ tt
∧-elim₁ {tt} proof = refl
∧-elim₁ {ff} ()


∧-elim₂ : ∀ {x y} → x ∧ y ≡ tt → y ≡ tt
∧-elim₂ {tt} {tt} proof = refl
∧-elim₂ {tt} {ff} ()
∧-elim₂ {ff} ()

∨-∧-absorp : ∀ {a b} → (a ∨ (a ∧ b)) ≡ tt → a ≡ tt
∨-∧-absorp {tt} p = refl
∨-∧-absorp {ff} ()

∧-∨-absorp : ∀ {a b} → (a ∧ (a ∨ b)) ≡ tt → a ≡ tt
∧-∨-absorp {tt} p = refl
∧-∨-absorp {ff} ()

∧-comm : ∀ {a b} → (a ∧ b) ≡ tt → (b ∧ a) ≡ tt
∧-comm {tt} {tt} p = refl
∧-comm {tt} {ff} ()
∧-comm {ff} ()



∨-comm : ∀ {a b} → (a ∨ b) ≡ tt → (b ∨ a) ≡ tt
∨-comm {tt} {tt} p = refl
∨-comm {tt} {ff} p = refl
∨-comm {ff} {tt} p = refl
∨-comm {ff} {ff} ()

𝔹-contra : ff ≡ tt → ∀ {P : Set} → P
𝔹-contra ()
