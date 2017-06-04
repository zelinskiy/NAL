
open import NAL.Data.Bool
open import NAL.Utils.Core renaming (_⊔_ to maxlevel)

module NAL.Data.Bool.Relations {ℓ : Level} {A : Set ℓ} (_≤_ : A → A → 𝔹) where

reflexive : Set ℓ
reflexive = ∀ {a : A} → a ≤ a ≡ tt

transitive : Set ℓ
transitive = ∀ {a b c : A} → a ≤ b ≡ tt → b ≤ c ≡ tt → a ≤ c ≡ tt

total : Set ℓ
total = ∀ {a b : A} → a ≤ b ≡ ff → b ≤ a ≡ tt

total→reflexive : total → reflexive
total→reflexive t {a} with inspect (a ≤ a)
... | tt with≡ p = p
... | ff with≡ p = t p

_⇔_ : A → A → 𝔹
a ⇔ b = a ≤ b ∧ b ≤ a

⇔-intro : ∀ {a b : A} → a ≤ b ≡ tt → b ≤ a ≡ tt → a ⇔ b ≡ tt
⇔-intro p q rewrite p | q = refl

_⊔_ : A → A → A
a ⊔ b = if a ≤ b then b else a

_⊓_ : A → A → A
a ⊓ b = if a ≤ b then a else b
