module NAL.Data.String where

open import NAL.Data.Char
open import NAL.Data.List
open import NAL.Data.Bool
open import NAL.Data.Nats
open import NAL.Data.Int
open import NAL.Data.Eq
open import NAL.Data.Comparable

open import NAL.Utils.Core

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringToList   : String → 𝕃 Char
  primStringFromList : 𝕃 Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → 𝔹
  primShowChar       : Char → String
  primShowString     : String → String
  primShowInteger    : ℤ -> String

showNat9 : ℕ → String
showNat9 n = primStringFromList (dropFirst (dropLast (primStringToList (primShowChar (primNatToChar (48 + n)))))) 



postulate
  Strings≡ : ∀{x y} → primStringEquality x y ≡ tt → x ≡ y
  primStringEqualityRefl : ∀{x} → primStringEquality x x ≡ tt
  primStringEqualitySym : ∀{x y} → primStringEquality x y ≡ tt → primStringEquality y x ≡ tt

instance
  EqString : Eq String
  EqString = record {_is_ = primStringEquality}

instance
  ComparableString : Comparable String
  ComparableString = record {compare = λ a b → compare (primStringToList a) (primStringToList b)}


      
