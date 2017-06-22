module NAL.Data.Comparable where

open import NAL.Data.List
open import NAL.Data.Nats
open import NAL.Data.Bool

data Ord : Set where
  LT GT EQ : Ord


record Comparable {ℓ}(A : Set ℓ) : Set ℓ where
  field
    compare : A → A → Ord
  _is_ : A → A → 𝔹
  a is b with compare a b
  ... | EQ = tt
  ... | _  = ff

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
