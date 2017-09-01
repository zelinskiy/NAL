module NAL.Utils.Core where

import Agda.Primitive

open Agda.Primitive public

infix 4 _≡_ 

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

sym : ∀ {ℓ} {A : Set ℓ} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans :  ∀ {ℓ} {A : Set ℓ} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl  = refl

cong :  ∀ {ℓ} {A : Set ℓ} → {a b : A} → {B : Set ℓ} → (f : A → B) →
  a ≡ b → (f a) ≡ (f b)
cong f refl = refl

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

data ⊥ : Set where


⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()

record ⊤ : Set where
  constructor ⊤-intro

