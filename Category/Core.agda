module NAL.Category.Core where

open import NAL.Utils.Core
open import NAL.Data.Nats
open import NAL.Data.List hiding (_×_)
open import NAL.Utils.Function renaming (_∘_ to _○_ )
open import NAL.Data.Pair


{-
TODO:
Laws
Instance arguments
Group universal property objects w their proofs (e.g. Products, Exponentialx, etc.)
-}

record SmallCategory : Set₁ where
  field
    Objects : Set
    Hom : (A B : Objects) → Set
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    ∘-assoc : ∀ {A B C D} → {f : Hom A B} → {g : Hom B C} → {h : Hom C D} →
              h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    id : {A : Objects} → Hom A A


record BigCategory {ℓ} : Set (lsuc (lsuc ℓ)) where
  field
    Objects : Set (lsuc ℓ)
    Hom : (A B : Objects) → Set ℓ
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    ∘-assoc : ∀ {A B C D} → {f : Hom A B} → {g : Hom B C} → {h : Hom C D} →
              h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    id : {A : Objects} → Hom A A

-- TODO : Laws
record CartesianClosed {ℓ} (Cat : BigCategory {ℓ} ) : Set (lsuc ℓ) where
  open BigCategory
  field
    _×_ : Objects Cat → Objects Cat → Objects Cat
    pr₁ : {A B : Objects Cat}  → (Hom Cat) (A × B) A
    pr₂ : {A B : Objects Cat} → (Hom Cat) (A × B) B
    
    _⇒_ : Objects Cat → Objects Cat → Objects Cat
    eval : ∀ {A B} → (Hom Cat) ((A ⇒ B) × A) B
    
    init : Objects Cat
    term : Objects Cat

--Examples

List-Cat : (A : Set) → SmallCategory
List-Cat A = record {
      Objects = 𝕃 A;
      Hom = λ xs ys → (𝕃 A → 𝕃 A);
      _∘_ = λ f g → f ○ g;
      ∘-assoc = refl;
      id = λ x → x }


ℕ-Cat : SmallCategory
ℕ-Cat = record {
      Objects = ℕ;
      Hom = λ A B → (ℕ → ℕ);
      _∘_ = λ f g → f ○ g;
      ∘-assoc = refl;
      id = λ x → x }

Hask-Cat : BigCategory
Hask-Cat = record {
      Objects = Set;
      Hom = λ A B → (A → B);
      _∘_ = λ f g → λ t → f (g t);
      ∘-assoc = refl;
      id = λ x → x }

open BigCategory public
Hask-Cat-Closed : CartesianClosed Hask-Cat
Hask-Cat-Closed = record {
      _×_ = ⟪_,_⟫;
      pr₁ = proj₁;
      pr₂ = proj₂;
      _⇒_ = λ a b → a → b;
      eval = λ p → (proj₁ p) (proj₂ p)  ;
      init = ⊥;
      term = ⊤ }


