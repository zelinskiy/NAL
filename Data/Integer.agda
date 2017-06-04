
module NAL.Data.Integer where

open import NAL.Data.Nats renaming (_+_ to _|+|_; _≤_ to _|≤|_; _*_ to _|*|_; +comm to |+-comm|; _==_ to _|==|_ ) hiding (+0; 0+)
open import NAL.Data.Bool
open import NAL.Utils.Core
open import NAL.Utils.Dependent using (Σ; Σ_,_; π₁; π₂)
open import NAL.Data.Either3
open import NAL.Data.Maybe

module Private where
  check : ℕ → Set
  check 0 = ⊤
  check (suc _) = 𝔹

open Private

data ℤ : Set where
  Int : (n : ℕ) → check n → ℤ

ℤ0 : ℤ
ℤ0 = Int 0 ⊤-intro

#+_ : ℕ → ℤ
#+ (suc n) = Int (suc n) tt
#+ 0 = Int 0 ⊤-intro


#-_ : ℕ → ℤ
#- (suc n) = Int (suc n) ff
#- 0 = Int 0 ⊤-intro


module Private2 where
    
  <∸suc : ∀ {x y : ℕ} → y < x ≡ tt → Σ ℕ (λ n → x ∸ y ≡ suc n)
  <∸suc {zero} {zero} ()
  <∸suc {zero} {suc y} ()
  <∸suc {suc x} {zero} p = Σ x , refl
  <∸suc {suc x} {suc y} p = <∸suc {x} {y} (<-suc2 y x p)
  
  diffℤ : ℕ → ℕ → ℤ
  diffℤ x y with ℕ-trichotomy {x} {y}
  ...          | Middle eq = ℤ0
  ...          | Left lt with <∸suc {y} {x} lt
  ...                        | Σ n , _ = Int (suc n) ff
  diffℤ x y    | Right gt with <∸suc {x} {y} gt
  ...                         | Σ n , _ =  Int (suc n) tt

open Private2

_+_ : ℤ → ℤ → ℤ
(Int 0 _) + y = y
x + (Int 0 _) = x
(Int (suc x) xsign) + (Int (suc y) ysign) with xsign xor ysign
... | ff = Int (suc x |+| suc y) xsign
... | tt = if xsign implies ysign then diffℤ y x else diffℤ x y

+0 : ∀ (x : ℤ) → x + Int 0 _ ≡ x
+0 (Int 0 _) = refl
+0 (Int (suc x) xsign) = refl

signum : ℤ → Maybe 𝔹
signum (Int 0 _) = Nothing
signum (Int (suc _) s) = Just s


+-comm : ∀ (x y : ℤ) → x + y ≡ y + x
+-comm (Int 0 _) y rewrite +0 y = refl
+-comm x (Int 0 _) = +0 x
+-comm (Int (suc x) xsign) (Int (suc y) ysign) with xsign xor ysign
... | ff = {!!}
... | tt = {!!}

_≤_ : ℤ → ℤ → 𝔹
(Int 0 _) ≤ (Int 0 _) = tt
Int 0 _ ≤ Int (suc _) ysign = ysign
Int (suc _) xsign ≤ Int 0 _ = ¬ xsign
Int (suc x) xsign ≤ Int (suc y) ysign with xsign xor ysign
... | tt = xsign implies ysign
... | ff = if xsign then x |≤| y else (y |≤| x)

_==_ : ℤ → ℤ → 𝔹
a == b = a ≤ b ∧ b ≤ a

==-implies-≡ : ∀ (x y : ℤ) → x == y ≡ tt → x ≡ y
==-implies-≡ x y p with inspect (x == y)
==-implies-≡ x y p | tt with≡ q = {!!}
==-implies-≡ x y p | ff with≡ q = {!!}


neg : ℤ → ℤ
neg (Int 0 _) = (Int 0 _)
neg (Int (suc x) s) = Int (suc x) (¬ s)

_-_ : ℤ → ℤ → ℤ
x - y = x + neg y

_*_ : ℤ → ℤ → ℤ
(Int 0 _) * (Int 0 _) = (Int 0 _)
(Int 0 _) * _ = (Int 0 _)
_ * (Int 0 _) = (Int 0 _)
(Int (suc x) xsign) * (Int (suc y) ysign) = Int (suc x |*| suc y) (xsign equiv ysign)
