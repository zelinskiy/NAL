
module NAL.Data.Pair where
open import NAL.Utils.Core


record ⟪_,_⟫ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor ⟨_,_⟩
  field
    proj₁ : A
    proj₂ : B 

open ⟪_,_⟫ public
