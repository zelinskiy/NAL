module NAL.Algebra.Functor where

open import NAL.Data.List
open import NAL.Utils.Function
open import NAL.Data.Bool
open import NAL.Data.Nats
open import NAL.Data.Maybe

open import NAL.Utils.Core

const : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A → B → A
const a _ = a

id : ∀ {ℓ} {A : Set ℓ} → A → A
id = λ x → x

record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
    law1 : ∀ {A} → (func : F A) → fmap id func ≡ id func
    law2 : ∀ {A B C} → (f : B → C) → (g : A → B) → (func : F A) → fmap (f ∘ g) func ≡ ((fmap f) ∘ (fmap g)) func
  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public


instance
  functorList : ∀ {ℓ} → Functor (𝕃 {ℓ})
  functorList = record {
    fmap = map;
    law1 = map-id;
    law2 = map-∘ }

instance
  functorMaybe : ∀ {ℓ} → Functor (Maybe {ℓ})
  functorMaybe = record {
    fmap = λ { f Nothing → Nothing; f (Just x) → Just (f x) };
    law1 = λ { Nothing → refl ; (Just x) → refl };
    law2 = λ { f g Nothing → refl ; f g (Just x) → refl } }

fmap2 : {A B : Set } {F : Set → Set} {G : Set → Set}
  {{r1 : Functor G }} {{r2 : Functor F}} →
  (A → B) → G (F A) → G (F B)
fmap2 = fmap ∘ fmap


list0 : 𝕃 ℕ
list0 = 1 :: 2 :: 3 :: 4 :: 5 :: []

list1 : 𝕃 (𝕃 ℕ)
list1 = list0 :: list0 :: list0 :: []

list3 : 𝕃 (𝕃 ℕ)
list3 = fmap2 (λ x → x + 1) list1
