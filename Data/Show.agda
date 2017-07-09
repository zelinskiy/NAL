module NAL.Data.Show where

open import NAL.Data.String
open import NAL.Data.Char

record Show {ℓ} (A : Set ℓ) : Set ℓ where
  field show : A → String

instance
  showChar : Show Char
  showChar = record {show = primShowChar}


instance
  showString : Show String
  showString = record {show = λ x → x}
