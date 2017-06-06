
module NAL.Data.Integer where

open import NAL.Data.Nats renaming (_+_ to _|+|_; _≤_ to _|≤|_; _*_ to _|*|_; +comm to |+-comm|; _==_ to _|==|_; _<_ to _|<|_) hiding (+0; 0+)
open import NAL.Data.Bool
open import NAL.Utils.Core
open import NAL.Utils.Dependent using (Σ; Σ_,_; π₁; π₂)
open import NAL.Data.Either3
open import NAL.Data.Maybe
open import NAL.Data.Pair

module Private where
  check : ℕ → Set
  check 0 = ⊤
  check (suc _) = 𝔹

open Private

data ℤ : Set where
  Int : (n : ℕ) → check n → ℤ

ℤ0 : ℤ
ℤ0 = Int 0 ⊤-intro

mkℤ : ℕ → ℤ
mkℤ 0 = Int 0 ⊤-intro
mkℤ (suc n) = Int (suc n) tt

#+_ : ℕ → ℤ
#+ (suc n) = Int (suc n) tt
#+ 0 = Int 0 ⊤-intro


#-_ : ℕ → ℤ
#- (suc n) = Int (suc n) ff
#- 0 = Int 0 ⊤-intro


module Private2 where
    
  <∸suc : ∀ {x y : ℕ} → y |<| x ≡ tt → Σ ℕ (λ n → x ∸ y ≡ suc n)
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

0+ : ∀ (x : ℤ) → x + Int 0 _ ≡ x
0+ (Int 0 _) = refl
0+ (Int (suc x) xsign) = refl

signum : ℤ → Maybe 𝔹
signum (Int 0 _) = Nothing
signum (Int (suc _) s) = Just s

lemma1 : ∀ {x y xsign ysign} → xsign xor ysign ≡ ff → (Int (suc x) xsign) + (Int (suc y) ysign) ≡ Int (suc x |+| suc y) xsign
lemma1 {x}{y}{tt}{tt} p = refl
lemma1 {x}{y}{ff}{tt} ()
lemma1 {x}{y}{tt}{ff} ()
lemma1 {x}{y}{ff}{ff} p = refl

lemma2 : ∀ {x y xsign ysign} →
  xsign xor ysign ≡ tt →
  xsign implies ysign ≡ tt →
  (Int (suc x) xsign) + (Int (suc y) ysign) ≡ diffℤ y x
lemma2 {x}{y}{tt}{tt} ()
lemma2 {x}{y}{ff}{tt} p q = refl
lemma2 {x}{y}{tt}{ff} p ()
lemma2 {x}{y}{ff}{ff} ()

lemma3 : ∀ {x y xsign ysign} →
  xsign xor ysign ≡ tt →
  xsign implies ysign ≡ ff →
  (Int (suc x) xsign) + (Int (suc y) ysign) ≡ diffℤ x y
lemma3 {x}{y}{tt}{tt} p ()
lemma3 {x}{y}{ff}{tt} p ()
lemma3 {x}{y}{tt}{ff} p q = refl
lemma3 {x}{y}{ff}{ff} p ()

lemma4 : ∀ {x y} → x xor y ≡ tt → x implies y ≡ tt → y implies x ≡ ff
lemma4 {tt} {tt} ()
lemma4 {tt} {ff} p ()
lemma4 {ff} {tt} p q = refl
lemma4 {ff} {ff} ()

lemma5 : ∀ {x y} → x xor y ≡ tt → x implies y ≡ ff → y implies x ≡ tt
lemma5 {tt} {tt} ()
lemma5 {ff} {tt} p ()
lemma5 {tt} {ff} p q = refl
lemma5 {ff} {ff} ()

+-comm : ∀ (x y : ℤ) → x + y ≡ y + x
+-comm (Int 0 _) y = sym(0+ y)
+-comm x (Int 0 _) = +0 x
+-comm (Int (suc x) xsign) (Int (suc y) ysign) with inspect (xsign xor ysign)
... | ff with≡ p rewrite
                      lemma1{x}{y}{xsign}{ysign} p
                    | lemma1{y}{x}{ysign}{xsign} (xor-comm{xsign}{ysign} p)
                    | +suc-lemma x y
                    | +suc-lemma y x
                    | |+-comm| x y
                    | xor-ff-equal {xsign} {ysign} p
                    = refl
+-comm (Int (suc x) xsign) (Int (suc y) ysign) | tt with≡ p with inspect (xsign implies ysign)
... | tt with≡ q rewrite
                      lemma2{x}{y}{xsign}{ysign} p q
                    | lemma3 {y} {x}{ysign}{xsign} (xor-comm{xsign}{ysign} p) (lemma4 p q)
                    = refl
... | ff with≡ q rewrite
                      lemma3{x}{y}{xsign}{ysign} p q
                    | lemma2 {y} {x}{ysign}{xsign} (xor-comm{xsign}{ysign} p) (lemma5 p q)
                    = refl

_≤_ : ℤ → ℤ → 𝔹
(Int 0 _) ≤ (Int 0 _) = tt
Int 0 _ ≤ Int (suc _) ysign = ysign
Int (suc _) xsign ≤ Int 0 _ = ¬ xsign
Int (suc x) xsign ≤ Int (suc y) ysign with xsign xor ysign
... | tt = xsign implies ysign
... | ff = if xsign then x |≤| y else (y |≤| x)

_==_ : ℤ → ℤ → 𝔹
a == b = a ≤ b ∧ b ≤ a

_<_ : ℤ → ℤ → 𝔹
a < b = if (a == b) then ff else (a ≤ b)

{-
==-implies-≡ : ∀ (x y : ℤ) → x == y ≡ tt → x ≡ y
==-implies-≡ x y p with inspect (x == y)
==-implies-≡ x y p | tt with≡ q = {!!}
==-implies-≡ x y p | ff with≡ q = {!!}
-}

neg : ℤ → ℤ
neg (Int 0 _) = (Int 0 _)
neg (Int (suc x) s) = Int (suc x) (¬ s)

_-_ : ℤ → ℤ → ℤ
x - y = x + neg y

abs : ℤ → ℤ
abs (Int 0 ⊤-intro) = Int 0 ⊤-intro
abs (Int (suc n) _) = Int (suc n) tt


_*_ : ℤ → ℤ → ℤ
(Int 0 _) * (Int 0 _) = (Int 0 _)
(Int 0 _) * _ = (Int 0 _)
_ * (Int 0 _) = (Int 0 _)
(Int (suc x) xsign) * (Int (suc y) ysign) = Int (suc x |*| suc y) (xsign equiv ysign)
