module MyAlgebra where

open import Utils using (⊥; _≡_; refl)
open import MyList using (𝕃; _::_; []; _∈ₙ_)
open import MyBool using (𝔹; tt; ff)
open import MyNats using (ℕ; _+_; +assoc; +0; 0+) renaming (suc to nsucc; zero to nzero)
open import MyDependent using (Σ; Σ_,_)



--PHILOSOPHY: Typeclasses are bad. So we use C-c C-v
--http://www.cs.nott.ac.uk/~psxpc2/away-day-2013/inheritance-overloading.pdf

---------------Magma----------------------
 
record Ω-Magma (M : Set) : Set where
  field
    _⊕_ : M → M → M

Magma : Set₁
Magma = Σ Set Ω-Magma


---------------Semigroup------------------

record Ω-Semigroup (S : Set) : Set  where
  field
    _⊕_ : S → S → S
    ⊕-assoc : (x y z : S) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z

Semigroup : Set₁
Semigroup = Σ Set Ω-Semigroup

---------------Monoid---------------------
record Ω-Monoid (M : Set) : Set  where
  field
    ε : M
    _⊕_ : M → M → M
    ⊕-assoc : (x y z : M) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    runit : (x : M) → x ⊕ ε ≡ x
    lunit : (x : M) → ε ⊕ x ≡ x

Monoid : Set₁
Monoid = Σ Set Ω-Monoid

---------------Group----------------------
record Ω-Group (G : Set) : Set  where
  field
    ε : G
    _⊕_ : G → G → G
    ⊕-assoc : (x y z : G) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    runit : (x : G) → x ⊕ ε ≡ x
    lunit : (x : G) → ε ⊕ x ≡ x
    _⁻ : G → G
    linv : ∀ (x : G) → (x ⁻) ⊕ x ≡ ε
    rinv : ∀ (x : G) → x ⊕ (x ⁻) ≡ ε

Group : Set₁
Group = Σ Set Ω-Group
---------------Abelian Group--------------
record Ω-AbelianGroup (G : Set) : Set  where
  field
    ε : G
    _⊕_ : G → G → G
    ⊕-assoc : (x y z : G) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    ⊕-comm : (x y : G) → x ⊕ y ≡ y ⊕ x
    runit : (x : G) → x ⊕ ε ≡ x
    lunit : (x : G) → ε ⊕ x ≡ x
    _⁻ : G → G
    linv : ∀ (x : G) → (x ⁻) ⊕ x ≡ ε
    rinv : ∀ (x : G) → x ⊕ (x ⁻) ≡ ε

AbelianGroup : Set₁
AbelianGroup = Σ Set Ω-AbelianGroup
---------------Ring-----------------------
--TODO : Split in 2 Abelian groups somehow

record Ω-Ring (G : Set) : Set  where
  field
    0# : G
    
    _⊕_ : G → G → G
    ⊕-assoc : (x y z : G) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    ⊕-comm : (x y : G) → x ⊕ y ≡ y ⊕ x
    
    ⊕-0# : (x : G) → x ⊕ 0# ≡ x
    0#-⊕ : (x : G) → 0# ⊕ x ≡ x

    _⁰ : G → G
    0#-linv : ∀ (x : G) → (x ⁰) ⊕ x ≡ 0#
    0#-rinv : ∀ (x : G) → x ⊕ (x ⁰) ≡ 0#
    
    1# : G

    _⊗_ : G → G → G
    ⊗-assoc : (x y z : G) → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    ⊗-comm : (x y : G) → x ⊗ y ≡ y ⊗ x

    ⊗-1# : (x : G) → x ⊗ 1# ≡ x
    1#-⊗ : (x : G) → 1# ⊗ x ≡ x

    _¹ : G → G
    1#-linv : ∀ (x : G) → (x ¹) ⊗ x ≡ 1#
    1#-rinv : ∀ (x : G) → x ⊗ (x ¹) ≡ 1#

    ⊗-ldistr-⊕ : (x y z : G) → x ⊗ (y ⊕ z) ≡ (x ⊗ y) ⊕ (x ⊗ z)
    -- ⊗-rdistr-⊕ can be derived easilly from ldistr and comm
    
    

Ring : Set₁
Ring = Σ Set Ω-Ring

---------------SemiLattice--------------------

record Ω-SemiLattice (L : Set) : Set where
  field
    _⋆_ : L → L → L
    ⋆-idemp : (x : L) → x ⋆ x ≡ x
    ⋆-assoc : (x y z : L) → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z
    ⋆-comm : (x y : L) → x ⋆ y ≡ y ⋆ x

SemiLattice : Set₁
SemiLattice = Σ Set Ω-SemiLattice
---------------Lattice--------------------
record Ω-Lattice (L : Set) : Set where
  field
    _⊔_ : L → L → L
    ⊔-idemp : (x : L) → x ⊔ x ≡ x
    ⊔-assoc : (x y z : L) → x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
    ⊔-comm : (x y : L) → x ⊔ y ≡ y ⊔ x


    _⊓_ : L → L → L
    ⊓-idemp : (x : L) → x ⊓ x ≡ x
    ⊓-assoc : (x y z : L) → x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
    ⊓-comm : (x y : L) → x ⊓ y ≡ y ⊓ x

    ⊔-absorp-⊓ : (x y : L) → x ⊔ (x ⊓ y) ≡ x
    -- Check if second absorption necessary?
    ⊓-absorp-⊔ : (x y : L) → x ⊓ (x ⊔ y) ≡ x

Lattice : Set₁
Lattice = Σ Set Ω-Lattice
---------------Heyting Algebra------------
-- Lattice with implication, 0, 1
-- Not finished
record Ω-HeytingAlgebra (L : Set) : Set where
  field
    _⊔_ : L → L → L
    ⊔-idemp : (x : L) → x ⊔ x ≡ x
    ⊔-assoc : (x y z : L) → x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
    ⊔-comm : (x y : L) → x ⊔ y ≡ y ⊔ x


    _⊓_ : L → L → L
    ⊓-idemp : (x : L) → x ⊓ x ≡ x
    ⊓-assoc : (x y z : L) → x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
    ⊓-comm : (x y : L) → x ⊓ y ≡ y ⊓ x

    ⊔-absorp-⊓ : (x y : L) → x ⊔ (x ⊓ y) ≡ x
    ⊓-absorp-⊔ : (x y : L) → x ⊓ (x ⊔ y) ≡ x

    1# : L
    
HeytingAlgebra : Set₁
HeytingAlgebra = Σ Set Ω-HeytingAlgebra

---------------Examples------------------




ℕ-Magma : Magma
ℕ-Magma = Σ ℕ , record { _⊕_ = _+_ }

ℕ-Monoid : Monoid
ℕ-Monoid = Σ ℕ , record {
    _⊕_ = _+_
  ; ε = 0
  ; ⊕-assoc = +assoc
  ; runit = +0
  ; lunit = 0+ }
