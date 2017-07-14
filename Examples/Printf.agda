module NAL.Examples.Printf where

open import NAL.Utils.Function
open import NAL.Utils.Core

open import NAL.Data.List
open import NAL.Data.Char
open import NAL.Data.String
open import NAL.Data.Nats
open import NAL.Data.Int
open import NAL.Data.Float
open import NAL.Data.Pair

data Format : Set where
  stringArg : Format
  intArg    : Format
  floatArg  : Format
  charArg   : Format
  litChar   : Char -> Format
  badFormat : Char -> Format

data BadFormat (c : Char) : Set where

format : String -> 𝕃 Format
format = format' ∘ primStringToList
  where
    format' : 𝕃 Char -> 𝕃 Format
    format' ('%' :: 's' :: fmt) = stringArg   :: format' fmt
    format' ('%' :: 'd' :: fmt) = intArg      :: format' fmt
    format' ('%' :: 'f' :: fmt) = floatArg    :: format' fmt
    format' ('%' :: 'c' :: fmt) = charArg     :: format' fmt
    format' ('%' :: '%' :: fmt) = litChar '%' :: format' fmt
    format' ('%' ::  c  :: fmt) = badFormat c :: format' fmt
    format' (c          :: fmt) = litChar c   :: format' fmt
    format'  []                = []

Printf' : 𝕃 Format -> Set
Printf' (stringArg   :: fmt) = ⟪ String , Printf' fmt ⟫
Printf' (intArg      :: fmt) = ⟪ ℤ , Printf' fmt ⟫
Printf' (floatArg    :: fmt) = ⟪ Float , Printf' fmt ⟫
Printf' (charArg     :: fmt) = ⟪ Char , Printf' fmt ⟫
Printf' (badFormat c :: fmt) = BadFormat c
Printf' (litChar _   :: fmt) = Printf' fmt
Printf'  []                 = ⊤

Printf : String -> Set
Printf fmt = Printf' (format fmt)

printf : (fmt : String) -> Printf fmt -> String
printf = printf' ∘ format
  where
    printf' : (fmt : 𝕃 Format) -> Printf' fmt -> String
    printf' (stringArg   :: fmt) (⟨ s , args ⟩) = primStringAppend s (printf' fmt args)
    printf' (intArg      :: fmt) (⟨ n , args ⟩) = primStringAppend (primShowInteger n) (printf' fmt args)
    printf' (floatArg    :: fmt) (⟨ x , args ⟩) = primStringAppend (primShowFloat x) (printf' fmt args)
    printf' (charArg     :: fmt) (⟨ c , args ⟩) = primStringAppend (primShowChar c) (printf' fmt args)
    printf' (litChar c   :: fmt) args       = primStringAppend (primStringFromList  [ c ]) (printf' fmt args)
    printf' (badFormat _ :: fmt) ()
    printf'  [] ⊤-intro = ""
