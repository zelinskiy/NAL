module NAL.Utils.Function where

open import NAL.Utils.Core

_∘_ : ∀ {ℓ} {A : Set ℓ}{B : A → Set ℓ}{C : {x : A} → B x → Set ℓ}
    → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

flip : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : A → B → Set ℓ₃} →
        ((a : A) → (b : B) → C a b) → ((b : B) → (a : A) → C a b)
flip f x y = f y x


Associative : ∀ {ℓ} {A : Set ℓ} → (A → A → A) → Set ℓ
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

Commutative : ∀ {ℓ} {A : Set ℓ} → (A → A → A) → Set ℓ
Commutative _∙_ = ∀ x y → (x ∙ y) ≡ (y ∙ x)

LeftDistributive : ∀ {ℓ} {A : Set ℓ} → (⊗ ⊕ : A → A → A) → Set ℓ
LeftDistributive _⊗_ _⊕_ = ∀ x y z → (x ⊗ (y ⊕ z)) ≡ ((x ⊗ y) ⊕ (x ⊗ z))

RightDistributive : ∀ {ℓ} {A : Set ℓ} → (⊗ ⊕ : A → A → A) → Set ℓ
RightDistributive _⊗_ _⊕_ = ∀ x y z → ((y ⊕ z) ⊗ x) ≡ ((y ⊗ x) ⊕ (z ⊗ x))

rdistr+comm→ldistr : ∀ {ℓ} {A : Set ℓ} → (_*_ _+_ : A → A → A) →
  Commutative _*_ →
  RightDistributive _*_ _+_ →
  LeftDistributive _*_ _+_
rdistr+comm→ldistr  _*_ _+_ *c d x y z
  rewrite
    *c x (y + z)
  | d x y z
  | *c y x
  | *c z x
  = refl

ldistr+comm→rdistr : ∀ {ℓ} {A : Set ℓ} → (_*_ _+_ : A → A → A) →
  Commutative _*_ →
  Commutative _+_ →
  LeftDistributive _*_ _+_ →
  RightDistributive _*_ _+_
ldistr+comm→rdistr  _*_ _+_ *c +c d x y z
  rewrite
    *c (y + z) x
  | d x y z
  | *c x y
  | *c x z
  = refl
