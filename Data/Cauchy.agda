module NAL.Data.Cauchy where

open import NAL.Data.Nats using (_+_; ℕ; suc; zero)
open import NAL.Data.Rational as ℚ using (ℚ; ℚ0; _<_; _≤_; abs; _-_; _/_)
open import NAL.Data.Integer as ℤ using (Int)
open import NAL.Utils.Core
open import NAL.Data.Bool
open import NAL.Utils.Dependent

--see PML 1984 p.28
--R ≡ (Σx ∈ N → Q) Cauchy(x)
--Cauchy(a) ≡ (∀e ∈ Q) (e > 0 ⊃ (∃m ∈ N) (∀n ∈ N) (|am+n − am| ≤ e)),
-- ∀ε. ε > 0 ⊃ ∃x. ∀y. |f(x + y) - f(x)| ≤ ε

Cauchy : (f : ℕ → ℚ) → Set
Cauchy f = (ε : ℚ) → ℚ0 < ε ≡ tt → Σ ℕ λ x → (y : ℕ) → abs (f (x + y) - f x) ≤ ε ≡ tt
 
ℝ = Σ (ℕ → ℚ) Cauchy

ℝ0 : ℝ
ℝ0 = Σ (λ x → ℚ0) , (λ e p → Σ 0 , (λ _ → helper e p))
  where
    helper : (e : ℚ) → ℚ0 < e ≡ tt → abs (ℚ0 - ℚ0) ≤ e ≡ tt
    helper (Int (suc x) tt / 0) p = refl
    helper (Int (suc x) tt / suc n) p = refl
    helper (Int (suc x) ff / 0) p = p
    helper (Int (suc x) ff / suc n) p = p
    helper (Int zero ⊤-intro / 0) p = refl
    helper (Int zero ⊤-intro / suc n) p = refl
