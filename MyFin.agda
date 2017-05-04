module MyFin where
open import MyNats using (ℕ; _+_; subtract; _≤_)
open import Utils
open import MyBool using (𝔹; tt; ff)
open import MyDependent using (Σ; Σ_,_)

Fin-ω : ℕ → ℕ → Set
Fin-ω m n with n ≤ m
... | tt = ℕ
... | ff = ⊥

--data Fin Σ ℕ (Fin-ω 20) : Set where
