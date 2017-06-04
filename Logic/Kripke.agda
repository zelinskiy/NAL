module NAL.Logic.Kripke where

open import NAL.Data.String
open import NAL.Data.List

data Formula : Set where
  var : String → Formula
  True : Formula
  _⊃_ : Formula → Formula → Formula
  _&_ : Formula → Formula → Formula

infixr 30 _⊃_
infixl 60 _&_

Context : Set
Context = 𝕃 Formula

data _⊢_ : Context → Formula → Set where
  assume : ∀ {Γ f} → (f :: Γ) ⊢ f
  weaken : ∀ {Γ f g} → Γ ⊢ f → (g :: Γ) ⊢ f
  ⊃-Intro : ∀ {Γ f g} → (f :: Γ) ⊢ g → Γ ⊢ f ⊃ g
  ⊃-Elim : ∀ {Γ f g} → Γ ⊢ f ⊃ g → Γ ⊢ f → Γ ⊢ g
  True-Intro : ∀ {Γ} → Γ ⊢ True
  &-Intro : ∀ {Γ f g} → Γ ⊢ f → Γ ⊢ g → Γ ⊢ f & g
  &-Elim1 : ∀ {Γ f g} → Γ ⊢ f & g → Γ ⊢ f
  &-Elim2 : ∀ {Γ f g} → Γ ⊢ f & g → Γ ⊢ g
  
