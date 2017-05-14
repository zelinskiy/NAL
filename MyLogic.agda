module MyLogic where

open import MyList using (_++_)


record Σ (A : Set) (B : A → Set) : Set where
  constructor <_,_>
  field
    fstΣ : A
    sndΣ : B fstΣ

open Σ public 
