module MyMonad where
open import Agda.Primitive
open import MyList

record Monad {ℓ₁ ℓ₂} (M : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  field
    return : ∀ {A} → A → M A
    bind : ∀ {A B} → M A → (A → M B) → M B

  _>>=_ : ∀ {A B} → M A → (A → M B) → M B
  M₁ >>= M₂ = bind M₁ M₂
  
  _>>_ : ∀ {A B} → M A → M B → M B
  M₁ >> M₂ = M₁ >>= λ _ → M₂

open Monad {{...}} public

monadList : Monad 𝕃
monadList = record {
      return = λ x →  x :: [];
      bind = λ xs f → concat (map f xs)}
