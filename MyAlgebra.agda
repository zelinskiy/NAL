module MyAlgebra where

open import Utils using (⊥; _≡_; refl)
open import MyList using (𝕃; _::_; []; _∈ₙ_)
open import MyBool using (𝔹; tt; ff)
open import MyNats using (ℕ; _+_) renaming (suc to nsucc; zero to nzero)
open import MyDependent using (Σ)

open import Agda.Primitive using (Level; _⊔_; lsuc)


---------------Magma----------------------
 
record Ω-Magma (M : Set) : Set where
  field
    _⊕_ : M → M → M

Magma : Set₁
Magma = Σ Set Ω-Magma


---------------Semigroup------------------

---------------Monoid---------------------
record Ω-Monoid (M : Set) : Set  where
  field
    ε : M
    _⊕_ : M → M → M
    runit : (x : M) → x ⊕ ε ≡ x
    lunit : (x : M) → ε ⊕ x ≡ x

Monoid : Set₁
Monoid = Σ Set Ω-Monoid
---------------Magma----------------------

---------------Group----------------------

---------------Abelian Group--------------

---------------Ring-----------------------

---------------Lattice--------------------

---------------Heyting Algebra------------


---------------Examples------------------



{-
ℕ-Magma : Magma
ℕ-Magma = Σ (Fin 10) , record { _⊕_ = fplus }
-}
