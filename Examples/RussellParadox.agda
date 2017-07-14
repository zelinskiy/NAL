{-#  OPTIONS --type-in-type #-}

module NAL.Examples.RussellParadox where

open import NAL.Data.Nats
open import NAL.Data.Bool

open import NAL.Utils.Core
open import NAL.Utils.Dependent

--  from http://www.cs.nott.ac.uk/~psztxa/g53cfr/l20.html/l20.html

data M : Set where
  m : (I : Set) → (I → M) → M

∅ : M
∅ = m ⊥ ⊥-elim

[∅] : M
[∅] = m ⊤ (λ _ → ∅)

[∅,[∅]] : M
[∅,[∅]] = m 𝔹 (λ x → if x then ∅ else [∅])

_∈_ : M → M → Set
a ∈ m I f = Σ I (λ i → a ≡ f i)

_∉_ : M → M → Set
a ∉ b = (a ∈ b) → ⊥

R : M
R = m (Σ M (λ a → a ∉ a)) π₁

lem-1 : ∀ {X} → X ∈ R → X ∉ X
lem-1 (Σ (Σ Y , Y∉Y) , refl) = Y∉Y

lem-2 : ∀ {X} →  X ∉ X → X ∈ R
lem-2 {X} X∉X = Σ (Σ X , X∉X) , refl

lem-3 : R ∉ R
lem-3 R∈R = lem-1 R∈R R∈R

contr : ⊥
contr = lem-3 (lem-2 lem-3)

