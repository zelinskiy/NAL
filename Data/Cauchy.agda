module NAL.Data.Cauchy where

open import NAL.Data.Nats using (_+_; ℕ; suc; zero)
open import NAL.Data.Rational as ℚ using (ℚ; ℚ0; _<_; _≤_; abs; _-_; _/_; mkℚ; _÷_) renaming (_+_ to _+ℚ_)
open import NAL.Data.Integer as ℤ using (Int; mkℤ) renaming (_+_ to _+ℤ_)
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
    helper ((Int (suc x) tt) / (Int (suc y) tt)) p = refl
    helper ((Int (suc x) ff) / (Int (suc y) tt)) p = p
    helper ((Int (suc x) tt) / (Int (suc y) ff)) p = refl
    helper ((Int (suc x) ff) / (Int (suc y) ff)) p = p             
    helper ((Int 0 ⊤-intro) / (Int (suc y) tt)) p = refl
    helper ((Int 0 ⊤-intro) / (Int (suc y) ff)) p = refl             
    helper ((Int (suc x) tt) / (Int 0 ⊤-intro)) p = refl
    helper ((Int (suc x) ff) / (Int 0 ⊤-intro)) p = p             
    helper ((Int 0 ⊤-intro) / (Int 0 ⊤-intro)) p = refl
    
{-
helper : (e : ℚ) → ℚ0 < e ≡ tt → (w : ℕ) → (abs (√2 (0 + w) - √2 0) ≤ e) ≡ tt
helper (Int (suc x) tt / Int (suc y) tt) p zero = refl
helper (Int (suc x) tt / Int (suc y) tt) p (suc w) rewrite helper (Int (suc x) tt / Int (suc y) tt) p w = {!!}  
helper (Int (suc x) ff / Int (suc y) tt) p zero = p
helper (Int (suc x) ff / Int (suc y) tt) p (suc w) = {!!}  
helper (Int (suc x) tt / Int (suc y) ff) p zero = refl
helper (Int (suc x) tt / Int (suc y) ff) p (suc w) = {!!}  
helper (Int (suc x) ff / Int (suc y) ff) p zero = p
helper (Int (suc x) ff / Int (suc y) ff) p (suc w) = {!!}         
helper (Int zero ⊤-intro / Int (suc y) tt) p zero = refl
helper (Int zero ⊤-intro / Int (suc y) tt) p (suc w) = {!!}  
helper (Int zero ⊤-intro / Int (suc y) ff) p zero = refl
helper (Int zero ⊤-intro / Int (suc y) ff) p (suc w) = {!!}    
helper (Int (suc x) tt / Int zero ⊤-intro) p zero = refl
helper (Int (suc x) tt / Int zero ⊤-intro) p (suc w) = {!!}  
helper (Int (suc x) ff / Int zero ⊤-intro) p zero = p
helper (Int (suc x) ff / Int zero ⊤-intro) p (suc w) = {!!}  
helper (Int zero ⊤-intro / Int zero ⊤-intro) p zero = refl
helper (Int zero ⊤-intro / Int zero ⊤-intro) p (suc w) = {!!}  
-}

√2 : ℕ → ℚ
√2 0 = mkℚ (mkℤ 1)
√2 (suc n) = (bn +ℚ two ÷ bn) ÷ two
  where
    two = (mkℚ (mkℤ 2))
    bn = √2 n

