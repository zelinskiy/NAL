module MyFunctor where

open import Agda.Primitive
open import MyList
open import MyBool
open import MyNats

const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A → B → A
const a _ = a

record Functor {ℓ₁ ℓ₂} (F : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public

functorList : Functor 𝕃
functorList = record { fmap = map }



