module NAL.Examples.LCHI.Part2 where

open import NAL.Data.String
open import NAL.Data.List
open import NAL.Data.ListSet renaming (_∪_ to _∪LS_; _∩_ to _∩LS_;  _─_ to _─LS_)
open import NAL.Data.Eq hiding (_is_)
open import NAL.Data.Comparable
open import NAL.Data.Fin
open import NAL.Data.Either
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
  Shift : ∀ {n Γ φ} → Γ ⊢ φ → shift n Γ ⊢ φ

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


module ⊢-examples where
  Ex1 : ∀ {φ} → [] ⊢ φ ⊃ φ
  Ex1 {φ} = ⊃I Ax

  Ex2 : ∀{φ ψ} → [] ⊢ φ ⊃ (ψ ⊃ φ)
  Ex2 {φ} {ψ} = ⊃I (⊃I (Weak Ax))

  Ex3 : ∀{φ ψ ν} → [] ⊢ (φ ⊃ (ψ ⊃ ν)) ⊃ (φ ⊃ ψ) ⊃ (φ ⊃ ν)
  Ex3 {φ} {ψ} {ν} = ⊃I (⊃I (⊃I (⊃E {Γ}{ψ}{ν} (⊃E{Γ}{φ}{ψ ⊃ ν}(Shift {3} {Γ} (Weak (Weak Ax))) Ax) (⊃E (Weak Ax) Ax))))
    where Γ = φ :: (φ ⊃ ψ) :: (φ ⊃ (ψ ⊃ ν)) :: []
  {-
  Ex4 : ∀{φ ψ} → [] ⊢ (φ ⊃ ψ) ⊃ (¬ ψ ⊃ ¬ φ)
  Ex4 {φ} {ψ} = ⊃I (⊃I (⊃I {!!}))
  -}


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

-- Def 2.3.5 misses absorption laws, why ???

record BooleanAlgebra {ℓ} (B : Set ℓ) : Set ℓ where
  field
   _∪_ _∩_ : B → B → B
   ─_ : B → B
   0' 1' : B
   -- Associativity
   ∪-assoc : Associative _∪_   
   ∩-assoc : Associative _∩_
   --Commutativity
   ∪-comm : Commutative _∪_
   ∩-comm : Commutative _∩_
   --Distributivity
   ∪-distr-∩ : RightDistributive _∪_ _∩_
   ∩-distr-∪ : RightDistributive _∩_ _∪_
   --Identity
   a∪0≡a : RightIdentity _∪_ 0'
   a∩1≡a : RightIdentity _∩_ 1'
   --Complement
   -a∪a≡1 : LeftComplement ─_ _∪_ 1'
   -a∩a≡0 : LeftComplement ─_ _∩_ 0'
   -- Absorption
   ∩-abs-∪ : LeftAbsorption _∩_ _∪_
   ∪-abs-∩ : LeftAbsorption _∪_ _∩_

-- Example : ⟨𝔹, OR, AND, NOT, 0, 1⟩
-- Example : ⟨Fin 2, max, min, 1 - x, 0, 1⟩


record HeytingAlgebra {ℓ} (B : Set ℓ) : Set ℓ where
  field
  --===Lattice part==
   _∪_ _∩_ : B → B → B      
   --Commutativity
   ∪-comm : Commutative _∪_
   ∩-comm : Commutative _∩_
    -- Associativity
   ∪-assoc : Associative _∪_   
   ∩-assoc : Associative _∩_
   -- Absorption
   ∩-abs-∪ : LeftAbsorption _∩_ _∪_
   ∪-abs-∩ : LeftAbsorption _∪_ _∩_
   --Idempotency
   ∪-idemp : Idempotent _∪_
   ∩-idemp : Idempotent _∩_   
   --===Bounded Lattice part===
   0' 1' : B
   --Identity
   a∪0≡a : RightIdentity _∪_ 0'
   a∩1≡a : RightIdentity _∩_ 1'
   --===Pseudo Complement===
   ─_ : B → B
   --===Relative Pseudo Complement===
   _⇒_ : B → B → B
   a⇒a≡1 : ∀ a → a ⇒ a ≡ 1'
   a∩a⇒b≡a∩b : ∀ a b → a ∩ (a ⇒ b) ≡ a ∩ b
   b∩a⇒b≡b : ∀ a b → b ∩ (a ⇒ b) ≡ b
   ⇒-dist : LeftDistributive _⇒_ _∩_
   ─a≡a⇒0 : ∀ a → ─ a ≡ a ⇒ 0'
   
  _≤_ : B → B → Set ℓ
  a ≤ b = b ⇒ a ≡ 1'
  {-
  ∪-deMorgan : ∀ a b → ─ (a ∪ b) ≡ (─ a) ∩ (─ b)
  ∪-deMorgan a b  = {!!}
  -}

module ℋ-semantics where
  _⟦_⟧ : ∀{ℓ}{ℋ : Set ℓ}{{_ : HeytingAlgebra ℋ}} → Valuation ℋ → Φ → ℋ
  _⟦_⟧ {{ha}} v (var p) = v p
  _⟦_⟧ {{ha}} v ⊥  = 0' where open HeytingAlgebra ha
  _⟦_⟧ {{ha}} v (φ ∨ ψ) = (v ⟦ φ ⟧) ∪ (v ⟦ ψ ⟧)  where open HeytingAlgebra ha
  _⟦_⟧ {{ha}} v (φ ∧ ψ) = (v ⟦ φ ⟧) ∩ (v ⟦ ψ ⟧) where open HeytingAlgebra ha
  _⟦_⟧ {{ha}} v (φ ⊃ ψ) = (v ⟦ φ ⟧) ⇒ (v ⟦ ψ ⟧) where open HeytingAlgebra ha

  _,_⊨_ : ∀{ℓ}(ℋ : Set ℓ) {{_ : HeytingAlgebra ℋ}} (v : Valuation ℋ) (φ : Φ) → Set ℓ
  _,_⊨_ ℋ {{ha}} v φ = v ⟦ φ ⟧ ≡ 1' where open HeytingAlgebra ha
  
  _⊨_ : ∀{ℓ}(ℋ : Set ℓ) {{_ : HeytingAlgebra ℋ}} (φ : Φ) → Set ℓ
  ℋ ⊨ φ = ∀ v → ℋ , v ⊨ φ 

  ⊨_ : ∀{ℓ} → Φ → Set (lsuc ℓ)
  ⊨ φ = ∀ ℋ v {{ha}} → _,_⊨_ ℋ {{ha}} v φ

  Ex1 : ∀ {φ} → ⊨_ {lzero} (φ ⊃ φ)
  Ex1 {φ} ℋ v {{ha}} with v ⟦ φ ⟧
  ... | φ' = a⇒a≡1 φ' where open HeytingAlgebra ha
{-
  Ex2 : ∀ {φ ψ} → ⊨_ {lzero} (φ ⊃ (ψ ⊃ φ))
  Ex2 {φ} {ψ} ℋ v {{ha}} with v ⟦ φ ⟧ | v ⟦ ψ ⟧
  ... | φ' | ψ' = {!!} where open HeytingAlgebra ha
-}
  _⊨ᵣ_ : ∀{ℓ} → Context → Φ → Set (lsuc ℓ)
  Γ ⊨ᵣ φ = ∀ ℋ v ha → (∀ ψ → ψ ∈ Γ → _,_⊨_ ℋ {{ha}} v ψ) → _,_⊨_ ℋ {{ha}} v φ

  postulate
    Completeness : ∀ Γ φ → Γ ⊢ φ → _⊨ᵣ_ {lzero} Γ φ
    Soundness : ∀ Γ φ → _⊨ᵣ_ {lzero} Γ φ → Γ ⊢ φ
  
record GodelAlgebra {ℓ} (G : Set ℓ) : Set ℓ where
  field
    heytingAlgebra : HeytingAlgebra G
    propGA : ∀ a b → HeytingAlgebra._∪_ heytingAlgebra a b ≡ HeytingAlgebra.1' heytingAlgebra → Either (a ≡ HeytingAlgebra.1' heytingAlgebra) (b ≡ HeytingAlgebra.1' heytingAlgebra)

BAisHA : ∀ {ℓ} {B : Set ℓ} → BooleanAlgebra B → HeytingAlgebra B
BAisHA ba = record
              { _∪_ = _∪_
              ; _∩_ = _∩_
              ; _⇒_ = λ x y → (─ x) ∪ y
              ; ─_ = ─_
              ; 0' = 0'
              ; 1' = 1'
              ; ∪-assoc = ∪-assoc
              ; ∪-comm = ∪-comm
              ; ∩-assoc = ∩-assoc
              ; ∩-comm = ∩-comm
              ; a∪0≡a = a∪0≡a
              ; a∩1≡a = a∩1≡a
              ; a⇒a≡1 = -a∪a≡1
              ; ⇒-dist = λ x y z → rdistr+comm→ldistr _∪_ _∩_ ∪-comm ∪-distr-∩ (─ x) y z
              ; a∩a⇒b≡a∩b = p1
              ; b∩a⇒b≡b = p2
              ; ∩-abs-∪ = ∩-abs-∪
              ; ∪-abs-∩ = ∪-abs-∩
              ; ∪-idemp = absorp+id→idemp _∪_ _∩_ 1' ∪-abs-∩ a∩1≡a
              ; ∩-idemp = absorp+id→idemp _∩_ _∪_ 0' ∩-abs-∪ a∪0≡a
              ; ─a≡a⇒0 = p3
              }
              where
                open BooleanAlgebra ba
                p1 :  ∀ a b → (a ∩ ((─ a) ∪ b)) ≡ (a ∩ b)
                p1 a b rewrite
                    ∩-comm a ((─ a) ∪ b)
                  | ∩-distr-∪ a (─ a) b
                  | -a∩a≡0 a
                  | ∪-comm 0' (b ∩ a)
                  | a∪0≡a (b ∩ a)
                  | ∩-comm b a
                  = refl
                p2 : ∀ a b → (b ∩ ((─ a) ∪ b)) ≡ b
                p2 a b rewrite
                   ∩-comm b ((─ a) ∪ b)
                 | ∩-distr-∪ b (─ a) b
                 | absorp+id→idemp _∩_ _∪_ 0' ∩-abs-∪ a∪0≡a b
                 | ∩-comm (─ a) b
                 | ∪-comm (b ∩ (─ a)) b
                 | ∪-abs-∩ b (─ a)
                 = refl
                p3 : ∀ a → (─ a) ≡ ((─ a) ∪ 0')
                p3 a rewrite a∪0≡a (─ a) = refl
