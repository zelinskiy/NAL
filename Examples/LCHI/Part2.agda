module NAL.Examples.LCHI.Part2 where

open import NAL.Data.String
open import NAL.Data.List
open import NAL.Data.ListSet renaming (_∪_ to _∪LS_; _∩_ to _∩LS_;  _─_ to _─LS_)
open import NAL.Data.Eq hiding (_is_)
open import NAL.Data.Comparable
open import NAL.Data.Bin
open import NAL.Data.Pair
open import NAL.Data.Nats hiding (≤-trans; ≤-refl; even) renaming (_≤_ to _≤ₙ_)
open import NAL.Data.Triple
open import NAL.Data.Either
open import NAL.Data.Show
open import NAL.Data.Maybe
open import NAL.Data.Bool renaming (¬_ to not𝔹; _∧_ to and𝔹; _∨_ to or𝔹)
open import NAL.Utils.Core renaming (⊥ to Bot)
open import NAL.Utils.Function

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

instance
  showΦ : Show Φ
  showΦ = record {show = helper}
    where
      helper : Φ → String
      helper (var x) = x
      helper (⊥) = "_|_"
      helper (φ ⊃ ψ) = primStringAppend (primStringAppend (helper ψ) " -> ") (helper ψ)
      helper (φ ∨ ψ) = primStringAppend (primStringAppend (helper ψ) " ‌\\/ ") (helper ψ)
      helper (φ ∧ ψ) = primStringAppend (primStringAppend (helper ψ) " /\\ ") (helper ψ)


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
  ⊃I : ∀ {Γ φ ψ} → φ :: Γ ⊢ ψ → Γ ⊢ φ ⊃ ψ
  ⊃E : ∀ {Γ φ ψ} → Γ ⊢ φ ⊃ ψ → Γ ⊢ φ → Γ ⊢ ψ
  
  ∧I : ∀ {Γ φ ψ} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ φ ∧ ψ
  ∧E₁ : ∀ {Γ φ ψ} → Γ ⊢ φ ∧ ψ → Γ ⊢ φ
  ∧E₂ : ∀ {Γ φ ψ} → Γ ⊢ φ ∧ ψ → Γ ⊢ ψ

  ∨I₁ : ∀ {Γ φ ψ} → Γ ⊢ φ → Γ ⊢ φ ∨ ψ
  ∨I₂ : ∀ {Γ φ ψ} → Γ ⊢ ψ → Γ ⊢ φ ∨ ψ
  ∨E : ∀ {Γ φ ψ ρ} → Γ ⊢ φ ∨ ψ → Γ ⊢ φ ⊃ ρ → Γ ⊢ ψ ⊃ ρ → Γ ⊢ ρ
  
  FalseE : ∀ {Γ φ ψ} → Γ ⊢ ¬ φ → Γ ⊢ φ ⊃ ψ

Valuation : ∀ {ℓ} → Set ℓ → Set ℓ
Valuation A = String → A

postulate
  Weak : ∀ {Γ φ ψ} → Γ ⊢ φ → ψ :: Γ ⊢ φ
  Sub : ∀ {Γ φ ψ p} → Γ ⊢ φ → map (_[ p := ψ ]) Γ ⊢ φ [ p := ψ ]
  Exchange : ∀ {n Γ φ} → Γ ⊢ φ → exchange n Γ ⊢ φ


module 𝔹-ExhaustiveValidityChecking where

  checkValidityEx : Φ → Valuation 𝔹 → 𝔹
  checkValidityEx (var x) v = v x
  checkValidityEx ⊥ v = ff
  checkValidityEx (f ⊃ g) v = or𝔹 (not𝔹 (checkValidityEx f v)) (checkValidityEx g v)
  checkValidityEx (f ∨ g) v = or𝔹 (checkValidityEx f v) (checkValidityEx g v)
  checkValidityEx (f ∧ g) v = and𝔹 (checkValidityEx f v) (checkValidityEx g v)

  getVariables : Φ → 𝕃 String
  getVariables f = nub (h f)
    where
      h : Φ → 𝕃 String
      h (var x) = [ x ]
      h ⊥ = []
      h (p ⊃ q) = h p ++ h q
      h (p ∨ q) = h p ++ h q
      h (p ∧ q) = h p ++ h q


  funFromPairs : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}{B : Set ℓ₂}{{_ : Comparable A}} →  B → 𝕃 ⟪ A , B ⟫ → (A → B)
  funFromPairs def xs a with lookup xs a
  ... | Just b = b
  ... | Nothing = def --This will newer happen though

  fillLeft : ∀ {ℓ} {A : Set ℓ} → A → ℕ → 𝕃 A → 𝕃 A
  fillLeft e 0 xs = xs
  fillLeft e (suc n) xs with (suc n) ≤ₙ length xs
  ... | tt = xs
  ... | ff = e :: fillLeft e n xs

  getPosVals : Φ → 𝕃 (Valuation 𝔹)
  getPosVals p = map (funFromPairs ff ∘ zipLists vs) (map btrans (range 0 (pred (2 ^ z))))
    where
      vs = getVariables p
      z = length vs
      btrans = (fillLeft ff z) ∘ to𝔹 ∘ fromℕ

  isValid : Φ → 𝔹
  isValid φ = and (map (checkValidityEx φ) (getPosVals φ))

  Exx0 = var "A" ⊃ (var "B" ⊃ var "A")
  Exx1 = var "A" ⊃ var "B" ⊃ var "C"




module ⊢-examples where
  Ex1 : ∀ {φ} → [] ⊢ φ ⊃ φ
  Ex1 {φ} = ⊃I Ax

  Ex2 : ∀{φ ψ} → [] ⊢ φ ⊃ (ψ ⊃ φ)
  Ex2 {φ} {ψ} = ⊃I (⊃I (Weak Ax))

  Ex3 : ∀{φ ψ ν} → [] ⊢ (φ ⊃ (ψ ⊃ ν)) ⊃ (φ ⊃ ψ) ⊃ (φ ⊃ ν)
  Ex3 {φ} {ψ} {ν} = ⊃I (⊃I (⊃I (⊃E {Γ}{ψ}{ν} (⊃E{Γ}{φ}{ψ ⊃ ν}(Exchange {3} {Γ} (Weak (Weak Ax))) Ax) (⊃E (Weak Ax) Ax))))
    where Γ = φ :: (φ ⊃ ψ) :: (φ ⊃ (ψ ⊃ ν)) :: []
  {-
  Ex5 : ∀ {φ ψ} → φ :: (φ ⊃ ψ) :: [] ⊢ ψ
  Ex5 = {!!}

  Ex4 : ∀{φ ψ} → (((φ ⊃ ψ) ⊃ φ) ⊃ φ) :: [] ⊢ φ ∨ ¬ φ 
  Ex4 {φ} {ψ} = ∨I₂ (⊃I {!!})
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

record KripkeModel (C : Set) : Set₁ where
  field
    _≤_ : C → C → Set
    _⊩_ : C → String → Set
    ≤-porder : PartialOrder _≤_
    ⊩-mono : ∀ {c c' p} → c ≤ c' → c ⊩ p → c' ⊩ p
  ≤-trans : Transitive _≤_
  ≤-trans = tripleA ≤-porder
  ≤-refl : Reflexive _≤_
  ≤-refl = tripleB ≤-porder

module KripkeSemantics where

  _,_⊨_ : ∀{C : Set} → (k : KripkeModel C) → C → Φ → Set
  k , w  ⊨ var x = w ⊩ x where open KripkeModel k
  k , w  ⊨ ⊥  = Bot
  k , w  ⊨ (f ⊃ g) = ∀ {w'} → w ≤ w' → k , w' ⊨ f → k , w' ⊨ g where open KripkeModel k
  k , w  ⊨ (f ∧ g) = ⟪ (k , w ⊨ f) , (k , w ⊨ g) ⟫
  k , w  ⊨ (f ∨ g) = Either (k , w ⊨ f) (k , w ⊨ g)

  ⊨-mono : ∀ {C : Set} {k : KripkeModel C} {w₁ w₂ : C} {φ : Φ} →
         KripkeModel._≤_ k w₁ w₂ →
         k , w₁ ⊨ φ →
         k , w₂ ⊨ φ
  ⊨-mono {k = k}{φ = var x} r p = KripkeModel.⊩-mono k r p
  ⊨-mono {φ = ⊥} r p = p
  ⊨-mono {k = k}{φ = a ⊃ b} r p r' p' = p (≤-trans r r') p' where open KripkeModel k
  ⊨-mono {φ = φ ∨ ψ} r (Left p) = Left (⊨-mono {φ = φ} r p)
  ⊨-mono {φ = φ ∨ ψ} r (Right p) = Right (⊨-mono {φ = ψ} r p)
  ⊨-mono {φ = φ ∧ ψ} r (⟨ φ' , ψ' ⟩) = ⟨ ⊨-mono {φ = φ} r φ' ,  ⊨-mono {φ = ψ} r ψ' ⟩

  _,_⊨ᵣ_ : ∀ {C : Set} → (k : KripkeModel C) → C → Context → Set
  k , w ⊨ᵣ [] = ⊤
  k , w ⊨ᵣ (f :: Γ) = ⟪ (k , w ⊨ f) , (k , w ⊨ᵣ Γ) ⟫
  
  ⊨ᵣ-mono : ∀ {C : Set}{k : KripkeModel C} {Γ : Context} {w₁ w₂ : C} →
            KripkeModel._≤_ k w₁ w₂ →
            k , w₁ ⊨ᵣ Γ →
            k , w₂ ⊨ᵣ Γ
  ⊨ᵣ-mono {C} {k} {[]} _ _ = ⊤-intro
  ⊨ᵣ-mono {C} {k} {f :: Γ} r ⟨ u , v ⟩ =
    ⟨ ⊨-mono {C} {k} {φ = f} r u , ⊨ᵣ-mono {C} {k} {Γ} r v ⟩
  
  _⊩_ : Context → Φ → Set₁
  Γ ⊩ f = ∀ {C : Set}{k : KripkeModel C} {w : C} → k , w ⊨ᵣ Γ → k , w ⊨ f
{-
  KripkeSound : ∀ {Γ : Context} {φ : Φ} → Γ ⊢ φ → Γ ⊩ φ
  KripkeSound Ax = proj₁
  KripkeSound (Weak p) g = KripkeSound p (proj₂ g)
  KripkeSound (Sub p₁) = {!!}
  KripkeSound (Shift p) = {!!}
  KripkeSound (⊃I p) g r u =  KripkeSound p ⟨ u , ⊨ᵣ-mono r g ⟩
  KripkeSound (⊃E p q) {C} {k} g = (KripkeSound p g) (KripkeModel.≤-refl k) (KripkeSound q g)
  KripkeSound (∧I p q) h = ⟨ KripkeSound p h , KripkeSound q h ⟩
  KripkeSound (∧E₁ p) h = proj₁ (KripkeSound p h)
  KripkeSound (∧E₂ p) h = proj₂ (KripkeSound p h)
  KripkeSound (∨I₁ p) {C} {k} {w} g = Left (KripkeSound p g)
  KripkeSound (∨I₂ p) {C} {k} {w} g = Right (KripkeSound p g)
  KripkeSound (∨E p q h) {C} {k} d with KripkeSound p d
  ... | Left x = (KripkeSound q d) (KripkeModel.≤-refl k) x
  ... | Right x = (KripkeSound h d) (KripkeModel.≤-refl k) x
  KripkeSound (FalseE p) q r h = {!!}
-}

module IPC where

  data IPC : Set where
    var' : String → IPC
    _⊃'_ : IPC → IPC → IPC

  data _⊢'_ : 𝕃 IPC → IPC → Set where
    Ax' : ∀ {Γ φ} → φ :: Γ ⊢' φ 
    ⊃I' : ∀ {Γ φ ψ} → φ :: Γ ⊢' ψ → Γ ⊢' φ ⊃' ψ
    ⊃E' : ∀ {Γ φ ψ} → Γ ⊢' φ ⊃' ψ → Γ ⊢' φ → Γ ⊢' ψ

  infix 6 _⊢'_
  infixr 10 _⊃'_

  embed : IPC → Φ
  embed (var' x) = var x
  embed (φ ⊃' ψ) = (embed φ) ⊃ (embed ψ)

  instance
    showIPC : Show IPC
    showIPC = record {show = helper}
      where
        helper : IPC → String
        helper (var' x) = x
        helper (φ ⊃' ψ) = primStringAppend (primStringAppend (helper ψ) " -> ") (helper ψ)

  open KripkeSemantics

  IPCcomp : ∀ {Γ φ} → Γ ⊢' φ → map embed Γ ⊩ embed φ
  IPCcomp Ax' = proj₁
  IPCcomp (⊃I' ip) g r u = IPCcomp ip ⟨ u , ⊨ᵣ-mono r g ⟩
  IPCcomp (⊃E' ip iq) {C} {k} g = (IPCcomp ip g) (KripkeModel.≤-refl k) (IPCcomp iq g)
