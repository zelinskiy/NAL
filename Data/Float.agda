module NAL.Data.Float where

open import NAL.Data.Nats hiding (_+_; _≤_)
open import NAL.Data.Bool
open import NAL.Data.Int
open import NAL.Data.String
open import NAL.Data.Eq
open import NAL.Data.Either
open import NAL.Utils.Core
open import NAL.Utils.Dependent

postulate Float : Set
{-# BUILTIN FLOAT Float #-}

primitive
  primFloatEquality : Float → Float → Bool
  primFloatNumericalEquality : Float → Float → Bool
  primFloatNumericalLess     : Float → Float → Bool
  primNatToFloat    : Nat → Float
  primFloatPlus     : Float → Float → Float
  primFloatMinus    : Float → Float → Float
  primFloatTimes    : Float → Float → Float
  primFloatNegate   : Float → Float
  primFloatDiv      : Float → Float → Float
  primFloatSqrt     : Float → Float
  primRound         : Float → Int
  primFloor         : Float → Int
  primCeiling       : Float → Int
  primExp           : Float → Float
  primLog           : Float → Float
  primSin           : Float → Float
  primCos           : Float → Float
  primTan           : Float → Float
  primASin          : Float → Float
  primACos          : Float → Float
  primATan          : Float → Float
  primATan2         : Float → Float → Float
  primShowFloat     : Float → String
  
ℝ = Float

_≤_ : ℝ → ℝ → Bool
x ≤ y = primFloatNumericalLess x y ∨ primFloatNumericalEquality y x
infixr 5 _≤_

_≥_ : ℝ → ℝ → Bool
x ≥ y = primFloatNumericalLess y x ∨ primFloatNumericalEquality y x

infixr 5 _≥_



_+_ = primFloatPlus

infixr 6 _+_

postulate primFloatNumericalEquality-sym : ∀ {a b} → primFloatNumericalEquality a b ≡ primFloatNumericalEquality b a


-- Inconisitency warning here!
postulate eq→≡ : ∀ {a b} → primFloatNumericalEquality a b ≡ tt → a ≡ b

instance
  eqℝ : Eq ℝ
  eqℝ = record { _is_ = primFloatNumericalEquality; is→≡ = eq→≡}

