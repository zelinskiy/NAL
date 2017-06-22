{-# OPTIONS --type-in-type #-}
module NAL.Examples.Girard where

-- http://www.cs.cmu.edu/~kw/scans/hurkens95tlca.pdf

⊥   = ∀ p → p
¬_  = λ A → A → ⊥
℘_  = λ A → A → Set
℘℘_ = λ A → ℘ ℘ A

U = (X : Set) → (℘℘ X → X) → ℘℘ X

τ : ℘℘ U → U
τ t = λ (X : Set) (f : ℘℘ X → X) (p : ℘ X) → t λ (x : U) → p (f (x X f))

σ : U → ℘℘ U
σ s = s U λ (t : ℘℘ U) → τ t

τσ : U → U
τσ x = τ (σ x)

Δ = λ (y : U) → ¬ (∀ (p : ℘ U) → σ y p → p (τσ y))
Ω = τ λ (p : ℘ U) → ∀ (x : U) → σ x p → p x

{-
loop : (A : Set) → A
loop = (λ (₀ : ∀ (p : ℘ U) → (∀ (x : U) → σ x p → p x) → p Ω) →
  (₀ Δ λ (x : U) (₂ : σ x Δ) (₃ : ∀ (p : ℘ U) → σ x p → p (τσ x)) →
  (₃ Δ ₂ λ (p : ℘ U) → (₃ λ (y : U) → p (τσ y)))) λ (p : ℘ U) →
  ₀ λ (y : U) → p (τσ y)) λ (p : ℘ U) (₁ : ∀ (x : U) → σ x p → p x) →
  ₁ Ω λ (x : U) → ₁ (τσ x)
-}
