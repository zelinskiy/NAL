
open import NAL.Utils.Core
open import NAL.Data.Pair 

module NAL.Utils.Relation {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (_R_ : A → A → Set ℓ₂) where

reflexive : Set (ℓ₁ ⊔ ℓ₂)
reflexive = ∀ {a : A} → a R a

transitive : Set (ℓ₁ ⊔ ℓ₂)
transitive = ∀ {a b c : A} → a R b → b R c → a R c

total : Set (ℓ₁ ⊔ ℓ₂)
total = ∀ {a b : A} → a R b → b R a

preorder : Set (ℓ₁ ⊔ ℓ₂)
preorder = ⟪ reflexive , transitive ⟫
