module MyTut where

open import MyBool using (𝔹; tt; ff)

--kek
data ℤ : 𝔹 → Set where
  Z : ℤ ff
  S : ∀ {neg1 : 𝔹} → (neg2 : 𝔹) → ℤ neg2 → ℤ neg2















----------------------------------------------------------------
--total bullshit
{-
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Char using (Char; _==_)
open import Data.List using (List)

data Term : Set where
  Λ_↦_ : Char → Term → Term
  _#_ : Term → Term → Term
  V : Char → Term

_∼_ : Term → Term → Bool
V a ∼ V b = b == a
(a # aa) ∼ (b # bb) = (a ∼ b) ∧ (aa ∼ bb)
(Λ x ↦ xx) ∼ (Λ y ↦ yy) = (x == y) ∧ (xx ∼ yy)
_ ∼ _ = false

term0 : Term
term0 = Λ 'x' ↦ Λ 'y' ↦ Λ 'z' ↦ (V 'x' # V 'z') # ( V 'y' # V 'z')



_[_:=_] : Term → Term → Term → Term
V y [ x := t] with (x ∼ y)
... | true = t
... | false = V y
(a # b) [ x := t ] = (a [ x := t ]) # (b [ x := t ])
Λ y ↦ s [ x := t ] with (y ~ x)
... | false with (x ∈ fv s ∧ y ∈ fv t)
...              | false = Λ y (s [ x := t])
... | _ | _  = ?
-}
