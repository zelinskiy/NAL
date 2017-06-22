module NAL.Data.Char where

open import NAL.Data.Bool
open import NAL.Data.Nats

postulate Char : Set
{-# BUILTIN CHAR Char #-}

primitive
  primIsLower primIsDigit primIsAlpha primIsSpace primIsAscii
    primIsLatin1 primIsPrint primIsHexDigit : Char → 𝔹
  primToUpper primToLower : Char → Char
  primCharToNat : Char → ℕ
  primNatToChar : ℕ → Char
  primCharEquality : Char → Char → 𝔹
