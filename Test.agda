open import MyNats using (ℕ; _+_; subtract; _≤_)
open import Utils
open import MyBool using (𝔹; tt; ff)
open import MyDependent using (Σ; Σ_,_)


gg : ∀ {ℓ} (A : Set ℓ) → Set ℓ
gg A = (A → A → A)


--mon : ∀ {ℓ} {A : Set ℓ} → Σ A (gg {ℓ})
