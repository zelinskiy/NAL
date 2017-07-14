{-# OPTIONS --no-positivity-check #-}
module NAL.Examples.CurryParadox where

open import NAL.Utils.Core using (⊥)

data CS (C : Set) : Set where
  cs : (CS C → C) → CS C

paradox : ∀ {C} → CS C → C
paradox (cs b) = b (cs b)

loop : ∀ {C} → C
loop = paradox (cs paradox)

contr : ⊥
contr = loop
