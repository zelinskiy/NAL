module MyVector where


data 𝕍 {ℓ} (A : Set ℓ) : (n : ℕ) → Set ℓ where
  [] : 𝕍 A ℤ
  _::_ : ∀ {n} (x : A) (xs : 𝕍 A n) → 𝕍 A (𝕊 n)
