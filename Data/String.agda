module NAL.Data.String where

open import NAL.Data.Char
open import NAL.Data.List
open import NAL.Data.Bool
open import NAL.Data.Eq

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringToList   : String → 𝕃 Char
  primStringFromList : 𝕃 Char → String
  primStringAppend   : String → String → String
  primStringEquality : String → String → 𝔹
  primShowChar       : Char → String
  primShowString     : String → String

instance
  EqString : Eq String
  EqString = record {_is_ = primStringEquality}
