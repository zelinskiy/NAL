module NAL.Examples.LCHI.Part2 where

open import NAL.Data.String
open import NAL.Data.List
open import NAL.Data.ListSet renaming (_∪_ to _∪LS_; _∩_ to _∩LS_;  _─_ to _─LS_)
open import NAL.Data.Eq hiding (_is_)
open import NAL.Data.Comparable
open import NAL.Data.Fin
open import NAL.Data.Bool renaming (¬_ to not𝔹; _∧_ to and𝔹; _∨_ to or𝔹)
open import NAL.Utils.Core renaming (⊥ to Bot)

infixr 20 ¬_
infixl 15 _∧_ _∨_
infixr 10 _⊃_
infixr 10 _⇔_

data Φ : Set where
  var : String → Φ
  ⊥ : Φ
  _⊃_ : Φ → Φ → Φ
  _∨_ : Φ → Φ → Φ
  _∧_ : Φ → Φ → Φ

¬_ : Φ → Φ
¬ a = a ⊃ ⊥

_⇔_ : Φ → Φ → Φ
a ⇔ b = a ⊃ b ∧ b ⊃ a

Context = 𝕃 Φ

_[_:=_] : Φ → String → Φ → Φ
var y [ x := ψ ] with y is x
...  | tt = ψ
...  | ff = var y
⊥ [ x := ψ ] = ⊥
(P ⊃ Q) [ x := ψ ] = (P [ x := ψ ] ) ⊃ ( Q [ x := ψ ] )
(P ∨ Q) [ x := ψ ] = (P [ x := ψ ] ) ∨ ( Q [ x := ψ ] )
(P ∧ Q) [ x := ψ ] = (P [ x := ψ ] ) ∧ ( Q [ x := ψ ] )


infix 5 _⊢_
data _⊢_ : Context → Φ → Set where
  Ax : ∀ {Γ φ} → φ :: Γ ⊢ φ
  Weak : ∀ {Γ φ ψ} → Γ ⊢ φ → ψ :: Γ ⊢ φ
  Sub : ∀ {Γ φ ψ p} → Γ ⊢ φ → map (_[ p := ψ ]) Γ ⊢ φ [ p := ψ ]

  ⊃I : ∀ {Γ φ ψ} → φ :: Γ ⊢ ψ → Γ ⊢ φ ⊃ ψ
  ⊃E : ∀ {Γ φ ψ} → Γ ⊢ φ ⊃ ψ → Γ ⊢ φ → Γ ⊢ ψ
  
  ∧I : ∀ {Γ φ ψ} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ φ ∧ ψ
  ∧E₁ : ∀ {Γ φ ψ} → Γ ⊢ φ ∧ ψ → Γ ⊢ φ
  ∧E₂ : ∀ {Γ φ ψ} → Γ ⊢ φ ∧ ψ → Γ ⊢ ψ

  ∨I₁ : ∀ {Γ φ ψ} → Γ ⊢ φ → Γ ⊢ φ ∨ ψ
  ∨I₂ : ∀ {Γ φ ψ} → Γ ⊢ ψ → Γ ⊢ φ ∨ ψ
  ∨E : ∀ {Γ φ ψ ρ} → Γ ⊢ φ ∨ ψ → φ :: Γ ⊢ ρ → ψ :: Γ ⊢ ρ → Γ ⊢ ρ
  
  FalseE : ∀ {Γ f g} → Γ ⊢ ¬ f → Γ ⊢ f ⊃ g

Valuation : ∀ {ℓ} → Set ℓ → Set ℓ
Valuation A = String → A

--𝔹 = Fin 2
module 𝔹-semantics where
  _⟦_⟧ : Valuation 𝔹 → Φ → 𝔹
  v ⟦ var p ⟧ = v p
  v ⟦ ⊥ ⟧ = ff
  v ⟦ φ ∨ ψ ⟧ = max (v ⟦ φ ⟧) (v ⟦ ψ ⟧)
  v ⟦ φ ∧ ψ ⟧ = min (v ⟦ φ ⟧) (v ⟦ ψ ⟧)
  v ⟦ φ ⊃ ψ ⟧ = max (not𝔹 (v ⟦ φ ⟧)) (v ⟦ ψ ⟧)

  data Tautology (φ : Φ) : Set where
    isTautology : (v : Valuation 𝔹) → v ⟦ φ ⟧ ≡ tt → Tautology φ




module ℛ-semantics where
  -- Arcane BS
  record FieldOfSets {ℓ}{A : Set ℓ}{{_ : Eq A}}
    (X : ListSet A)(ℛ : ListSet (ListSet A)) : Set ℓ where
    constructor FOS
    field  
      isClosed∪ : {A B : ListSet A} → A ⊆? X ≡ tt → B ⊆? X ≡ tt →
        A ∈? ℛ ≡ tt → B ∈? ℛ ≡ tt → (A ∪LS B) ∈? ℛ ≡ tt
      isClosed∩ : {A B : ListSet A} → A ⊆? X ≡ tt → B ⊆? X ≡ tt →
        A ∈? ℛ ≡ tt → B ∈? ℛ ≡ tt → (A ∩LS B) ∈? ℛ ≡ tt
      isClosed─ : {A B : ListSet A} → A ⊆? X ≡ tt →  A ∈? ℛ ≡ tt →
        (X ─LS A) ∈? ℛ ≡ tt
    getX : ListSet A
    getX = X

  _⟦_⟧ : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}}{X : ListSet A}
    {ℛ : ListSet (ListSet A)}{{_ : FieldOfSets X ℛ}} →
    Valuation (ListSet A) → Φ → ListSet A
  v ⟦ var p ⟧ = v p
  v ⟦ ⊥ ⟧ = mkLS []
  _⟦_⟧  {{eq}} {{fos}} v (φ ∨ ψ) =
    (_⟦_⟧ {{eq}} {{fos}} v φ) ∪LS (_⟦_⟧  {{eq}} {{fos}} v ψ)
  _⟦_⟧  {{eq}} {{fos}} v (φ ∧ ψ) =
    (_⟦_⟧ {{eq}} {{fos}} v φ) ∩LS (_⟦_⟧  {{eq}} {{fos}} v ψ)
  _⟦_⟧  {{eq}} {{fos}} v (φ ⊃ ψ) =
    (FieldOfSets.getX fos ─LS _⟦_⟧ {{eq}} {{fos}} v φ) ∪LS (_⟦_⟧  {{eq}} {{fos}} v ψ)

  open 𝔹-semantics renaming (_⟦_⟧ to _⟦_⟧𝔹)

  postulate
    Tauto→ℛ :
      ∀{ℓ}
      {A : Set ℓ}
      {{eq : Eq A}}
      {X : ListSet A}
      {ℛ : ListSet (ListSet A)}{{fos : FieldOfSets X ℛ}} →
      (φ : Φ) → Tautology φ →  (v : Valuation (ListSet A)) →
      _⟦_⟧ {{eq}} {{fos}} v φ ≡ X
    ℛ→Tauto :
      ∀{ℓ}
      {A : Set ℓ}
      {{eq : Eq A}}
      {X : ListSet A}
      {ℛ : ListSet (ListSet A)}
      {{fos : FieldOfSets X ℛ}} →
      (φ : Φ) →
      (v : Valuation (ListSet A)) →
      _⟦_⟧ {{eq}} {{fos}} v φ ≡ X →
      Tautology φ 



open import NAL.Utils.Function


record BooleanAlgebra {ℓ} (B : Set ℓ) : Set ℓ where
  field
   _∪_ _∩_ : B → B → B
   ─_ : B → B
   0' 1' : B
   ∪-assoc : Associative _∪_
   ∪-comm : Commutative _∪_
   ∩-assoc : Associative _∩_
   ∩-comm : Commutative _∩_
   ∪-distr-∩ : RightDistributive _∪_ _∩_
   ∩-distr-∪ : RightDistributive _∩_ _∪_
   a∪0≡a : ∀ a → a ∪ 0' ≡ a
   a∩1≡a : ∀ a → a ∩ 1' ≡ a
   -a∪a≡1 : ∀ a → (─ a) ∪ a ≡ 1'
   -a∩a≡0 : ∀ a → (─ a) ∩ a ≡ 0'

-- Example : ⟨𝔹, OR, AND, NOT, 0, 1⟩
-- Example : ⟨Fin 2, max, min, 1 - x, 0, 1⟩


-- define a ≤ b iff a ∪ b = b
record HeytingAlgebra {ℓ} (B : Set ℓ) : Set ℓ where
  field
   _∪_ _∩_ _⇒_ _≤_ : B → B → B
   ─_ : B → B
   0' 1' : B
   ∪-assoc : Associative _∪_
   ∪-comm : Commutative _∪_
   ∩-assoc : Associative _∩_
   ∩-comm : Commutative _∩_
   ∪-distr-∩ : RightDistributive _∪_ _∩_
   ∩-distr-∪ : RightDistributive _∩_ _∪_
   a∪0≡a : ∀ a → a ∪ 0' ≡ a
   a∩1≡a : ∀ a → a ∩ 1' ≡ a
   a∪a≡a : ∀ a → a ∪ a ≡ a
   -a≡a⇒0 : ∀ a → (─ a) ≡ a ⇒ 0'
   -- must be (a ∩ c) ≤ b ⇆ c ≤ (a ⇒ b)
   a∩c≤b : ∀ a b c → (a ∩ c) ≤ b ≡ c ≤ (a ⇒ b)

module ℋ-semantics where
  _⟦_⟧ : ∀{ℓ}{ℋ : Set ℓ}{{_ : HeytingAlgebra ℋ}} → Valuation ℋ → Φ → ℋ
  _⟦_⟧ v (var p) = v p
  _⟦_⟧ {{ha}} v ⊥  = 0' ha where open HeytingAlgebra
  _⟦_⟧ {{ha}} v (φ ∨ ψ) = HeytingAlgebra._∪_ ha (v ⟦ φ ⟧) (v ⟦ ψ ⟧)
  _⟦_⟧ {{ha}} v (φ ∧ ψ) = HeytingAlgebra._∩_ ha (v ⟦ φ ⟧) (v ⟦ ψ ⟧)
  _⟦_⟧ {{ha}} v (φ ⊃ ψ) = HeytingAlgebra._⇒_ ha (v ⟦ φ ⟧) (v ⟦ ψ ⟧)
    
