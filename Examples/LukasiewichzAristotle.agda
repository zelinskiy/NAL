module NAL.Examples.LukasiewichzAristotle where

open import NAL.Data.List

postulate V : Set

data Φ : Set where
  A I : V → V → Φ
  _⊃_ _&_ _∨_ : Φ → Φ → Φ
  ~_ : Φ → Φ

E : V → V → Φ
E a b = ~ (A a b)

O : V → V → Φ
O a b = ~ (I a b)

Context = 𝕃 Φ

data ⊢_ : Φ → Set where
  FS1 : ∀ {a} → ⊢ A a a
  FS2 : ∀ {a} → ⊢ I a a
  FS3 : ∀ {a b c} → ⊢ ((A b c & A a b) ⊃ A a c)
  FS4 : ∀ {a b c} → ⊢ ((A b c & I b a) ⊃ I a c)
  MP : ∀ {A B} → ⊢ A → ⊢ (A ⊃ B) → ⊢ B

infixr 1 ⊢_

Celarent : ∀ {a b c} → ⊢ ((E b c) &  (A a b))  ⊃ (E a c)
Celarent {a} {b} {c} = MP {!!} {!!}
