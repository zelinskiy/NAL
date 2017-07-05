module NAL.Data.Triple where

open import NAL.Utils.Core

data Triple {ℓ₁ ℓ₂ ℓ₃} (A : Set ℓ₁) (B : Set ℓ₂) (C : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  mkTriple : A → B → C → Triple A B C
  
tripleA : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → Triple A B C → A
tripleA (mkTriple a _ _) = a
tripleB : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → Triple A B C → B
tripleB (mkTriple _ b _) = b
tripleC : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → Triple A B C → C
tripleC (mkTriple _ _ c) = c
