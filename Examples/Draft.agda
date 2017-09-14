module NAL.Examples.Draft where

open import NAL.Data.Nats
open import NAL.Data.List
open import NAL.Data.Maybe
open import NAL.Utils.Function

data Expr : Set where
  Enum : ℕ → Expr
  Eadd Emul : Expr

Stack = 𝕃 Expr

foldl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}{B : Set ℓ₂} → (B → A → B) → B → 𝕃 A → B
foldl f i [] = i
foldl f i (x :: xs) = f (foldl f i xs) x

head : ∀ {ℓ} {T : Set ℓ} → 𝕃 T → Maybe T
head [] = Nothing
head (x :: _) = Just x

{-# TERMINATING #-}
compute : Stack → Maybe Expr
compute = head ∘ foldl φ []
  where
   φ : Stack → Expr → Stack
   φ (Enum a :: Enum b :: s) Eadd = Enum (a + b) :: s
   φ (Enum a :: Enum b :: s) Emul = Enum (a * b) :: s
   φ s (Enum n) = Enum n :: s
   φ s e = e :: s

test1 = compute (Enum 11 :: Enum 22 :: Enum 33 :: Eadd :: Emul :: [])
