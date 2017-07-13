module NAL.Examples.RussellPope where

open import NAL.Data.Fin
open import NAL.Data.Vector

open import NAL.Utils.Core

postulate
  Nonsense : zero {1} ≡ suc (zero{0})
  Human : Set
  Russell : Human
  Pope : Human

list : 𝕍 Human 2
list = Russell :: Pope :: []

RussellIsPope : Russell ≡ Pope
RussellIsPope = cong (list !_) Nonsense
