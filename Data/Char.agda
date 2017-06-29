module NAL.Data.Char where

open import NAL.Data.Bool
open import NAL.Data.Nats
open import NAL.Data.Comparable

postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → 𝔹
  primToUpper primToLower : Char → Char
  primCharToNat : Char → ℕ
  primNatToChar : ℕ → Char
  primCharEquality : Char → Char → 𝔹

instance
  ComparableChar : Comparable Char
  ComparableChar = record {compare = λ a b → compare (primCharToNat a) (primCharToNat b)}
