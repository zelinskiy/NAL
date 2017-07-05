module NAL.Data.Comparable where

open import NAL.Data.List
open import NAL.Data.Pair
open import NAL.Data.Maybe
open import NAL.Data.Nats
open import NAL.Data.Bool
open import NAL.Utils.Core


data Ord : Set where
  LT GT EQ : Ord


record Comparable {ℓ}(A : Set ℓ) : Set ℓ where
  field
    compare : A → A → Ord
  _is_ : A → A → 𝔹
  a is b with compare a b
  ... | EQ = tt
  ... | _  = ff
  max : A → A → A
  max a b with compare a b
  ... | LT = b
  ... | _ = a
  min : A → A → A
  min a b with compare a b
  ... | GT = b
  ... | _ = a
  

open Comparable {{...}} public

instance
  OrdComparable : Comparable Ord
  OrdComparable = record { compare = cmp }
    where
      cmp : Ord → Ord → Ord
      cmp LT LT = EQ
      cmp LT _ = LT
      cmp GT GT = EQ
      cmp GT _ = GT
      cmp EQ LT = GT
      cmp EQ GT = LT
      cmp EQ EQ = EQ

instance
  ℕComparable : Comparable ℕ
  ℕComparable = record { compare = cmp }
    where
      cmp : ℕ → ℕ → Ord
      cmp zero zero = EQ
      cmp zero (suc y) = LT
      cmp (suc x) zero = GT
      cmp (suc x) (suc y) = cmp x y

instance
  𝔹Comparable : Comparable 𝔹
  𝔹Comparable = record { compare = cmp }
    where
      cmp : 𝔹 → 𝔹 → Ord
      cmp tt tt = EQ
      cmp ff ff = EQ
      cmp tt ff = GT
      cmp ff tt = LT
      

instance
  𝕃Comparable : ∀{ℓ}{A : Set ℓ}{{_ : Comparable A}} → Comparable (𝕃 A)
  𝕃Comparable = record { compare = cmp }
    where
      cmp : ∀{ℓ}{A : Set ℓ}{{_ : Comparable A}} → 𝕃 A → 𝕃 A → Ord
      cmp [] [] = EQ
      cmp [] (y :: ys) = LT
      cmp (x :: xs) [] = GT
      cmp (x :: xs) (y :: ys) with compare x y
      ... | EQ = cmp xs ys
      ... | o = o

lookup : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂} {{_ : Comparable A}} → 𝕃 ⟪ A , B ⟫ → A → Maybe B
lookup [] x = Nothing
lookup (⟨ a , b ⟩ :: r) x = if a is x then Just b else lookup r x
