module NAL.Utils.Function where

open import NAL.Data.Pair
open import NAL.Utils.Core
open import NAL.Utils.Dependent

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

LeftAbsorption : ∀ {ℓ} {A : Set ℓ} → (⊗ ⊕ : A → A → A) → Set ℓ
LeftAbsorption _⊗_ _⊕_ = ∀ a b → a ⊗ (a ⊕ b) ≡ a

RightIdentity : ∀ {ℓ} {A : Set ℓ} → (A → A → A) → A → Set ℓ
RightIdentity _∙_ ε = ∀ a → a ∙ ε ≡ a

LeftIdentity : ∀ {ℓ} {A : Set ℓ} → (A → A → A) → A → Set ℓ
LeftIdentity _∙_ ε = ∀ a → ε ∙ a ≡ a

Idempotent : ∀ {ℓ} {A : Set ℓ} → (A → A → A) → Set ℓ
Idempotent _∙_ = ∀ a → a ∙ a ≡ a


LeftComplement : ∀ {ℓ} {A : Set ℓ} → (A → A) → (A → A → A) → A → Set ℓ
LeftComplement ¬_ _∙_ ε = ∀ a → (¬ a) ∙ a ≡ ε

RightComplement : ∀ {ℓ} {A : Set ℓ} → (A → A) → (A → A → A) → A → Set ℓ
RightComplement ¬_ _∙_ ε = ∀ a → a ∙ (¬ a) ≡ ε

--TODO : x, y - unique
LatinSquare : ∀ {ℓ} {A : Set ℓ} → (A → A → A) → Set ℓ
LatinSquare {ℓ} {A} _∙_ = (a b : A) → Σ {ℓ} {ℓ} ⟪ A , A ⟫ (λ  {⟨ x , y ⟩ →  ⟪ a ∙ x ≡ b , y ∙ a ≡ b ⟫})

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

private
  lemma1 : ∀ {ℓ} {A : Set ℓ} →
    (_*_ _+_ : A → A → A) →
    (0' : A) →
    RightIdentity _+_ 0' →
    (∀ a b → a * b ≡ a * (b + 0'))
  lemma1 _*_ _+_ 0' p a b rewrite p b = refl

absorp+id→idemp : ∀ {ℓ} {A : Set ℓ} →
  (_*_ _+_ : A → A → A) →
  (0' : A) →
  LeftAbsorption _*_ _+_ →
  RightIdentity _+_ 0' →
  Idempotent _*_
absorp+id→idemp _*_ _+_ 0' abs rid a rewrite lemma1 _*_ _+_ 0' rid a a | abs a 0' = refl


comm+lid→rid : ∀ {ℓ} {A : Set ℓ} →
  (_+_ : A → A → A) →
  (0' : A) →
  Commutative _+_ →
  LeftIdentity _+_ 0' →
  RightIdentity _+_ 0'
comm+lid→rid _+_ 0' comm lid a rewrite comm a 0' | lid a = refl

comm+rid→lid : ∀ {ℓ} {A : Set ℓ} →
  (_+_ : A → A → A) →
  (0' : A) →
  Commutative _+_ →
  RightIdentity _+_ 0' →
  LeftIdentity _+_ 0'
comm+rid→lid _+_ 0' comm rid a rewrite comm 0' a | rid a = refl
