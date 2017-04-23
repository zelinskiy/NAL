module MyBool where

open import Agda.Builtin.Equality


data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹


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

infixl 5 _⊕_

_⊕_ : 𝔹 → 𝔹 → 𝔹
tt ⊕ b  = tt
a  ⊕ tt = tt
a  ⊕ b  = ff

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
