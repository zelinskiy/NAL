module MyAlgebra where

open import Utils using (⊥)
open import MyList using (𝕃; _::_; []; _∈ₙ_)
open import MyBool using (𝔹; tt; ff)
open import MyNats using (ℕ; _+_)

record Σ (A : Set) (B : A → Set) : Set where
  constructor Σ_,_
  field
    Σfst : A
    Σsnd : B Σfst

--mkArr : {A : Set} (a : A) → (a → a)
--mkArr = λ x → x

--data magma (A : Set) (B : λ a → (a → a → a)) : Σ A B  where 




allDistinct : 𝕃 ℕ → 𝔹
allDistinct [] = tt
allDistinct (x :: xs) with x ∈ₙ xs
... | tt = ff
... | ff = allDistinct xs

ℕ-semigroup-Ω : 𝕃 ℕ → Set
ℕ-semigroup-Ω [] = ⊥
ℕ-semigroup-Ω  xs with allDistinct xs
... | ff = ⊥
... | tt = ℕ → ℕ → ℕ


ℕ-semigroup₀ : Σ (𝕃 ℕ) ℕ-semigroup-Ω
ℕ-semigroup₀ = Σ 1 :: 2 :: 3 :: 4 :: [] , _+_







