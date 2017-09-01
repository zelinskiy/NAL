module NAL.Data.Eq where

open import NAL.Data.Bool
open import NAL.Data.Nats

open import NAL.Utils.Core


record Eq {ℓ}(A : Set ℓ) : Set ℓ where
  field
    _is_ : A → A → 𝔹
    is→≡ : ∀ {a b} → a is b ≡ tt → a ≡ b

open Eq {{...}} public

instance
  Eqℕ : Eq ℕ
  Eqℕ = record { _is_ = h; is→≡ = g}
    where
      h : ℕ → ℕ → 𝔹
      h 0 0 = tt
      h (suc x) (suc y) = h x y
      h _ _ = ff
      g : {a b : ℕ} → h a b ≡ tt → a ≡ b
      g {zero} {zero} p = refl
      g {zero} {suc b} p = 𝔹-contra p
      g {suc a} {zero} p = 𝔹-contra p
      g {suc a} {suc b} p = cong suc (g p)

instance
  Eq𝔹 : Eq 𝔹
  Eq𝔹 = record {_is_ = h; is→≡ = g}
    where
      h : 𝔹 → 𝔹 → 𝔹
      h tt tt = tt
      h ff ff = tt
      h _  _  = ff
      g : {a b : 𝔹} → h a b ≡ tt → a ≡ b
      g {tt} {tt} _ = refl
      g {tt} {ff} p = 𝔹-contra p
      g {ff} {tt} p = 𝔹-contra p
      g {ff} {ff} _ = refl

