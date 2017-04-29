module MyCat where

open import Utils
open import MyNats
open import MyList

record Category : Set1 where
  field
    Objects : Set
    Hom : (A B : Objects) → Set
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    ∘-assoc : ∀ {A B C D} → {f : Hom A B} → {g : Hom B C} → {h : Hom C D} →
              h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    id : {A : Objects} → Hom A A


record ℂ : Set where
  field
    re : ℕ
    im : ℕ

r0 : ℂ
r0 = record { re = 10; im = 5 }

ℕ-Cat : Category
ℕ-Cat = record {
      Objects = 𝕃 ℕ;
      Hom = (_⊆_);
      _∘_ = ?;
      ∘-assoc = ?;
      id = 
}
