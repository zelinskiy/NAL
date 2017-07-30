module NAL.Utils.Dependent where

open import NAL.Utils.Core using (_⊔_)

record Σ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor Σ_,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

ΠΣ : {A : Set} {B : A → Set} → Π A B → (a : A) → Σ A B
ΠΣ f x = Σ x , f x

private data R {A B : Set} (a : A) (b : B) : Set where

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B


--Axiom of Choice!
ac : {A B : Set} →
  ((a : A) → Σ B (λ b → R a b )) →
  Σ (A → B) (λ f → ((a : A) → R a (f a)))
ac g = Σ (λ a → π₁ (g a)) , (λ a → π₂ (g a))


