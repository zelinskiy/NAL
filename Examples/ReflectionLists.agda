module  NAL.Examples.ReflectionLists where

open import NAL.Data.List
open import NAL.Data.Bool
open import NAL.Data.Nats
open import NAL.Utils.Function
open import NAL.Utils.Core

--infixr 40 _|::|_
--infixl 30 _|++|_

data |𝕃| : Set → Set₁ where
  toRep : {A : Set} → 𝕃 A → |𝕃| A
  _|++|_ : {A : Set} → |𝕃| A → |𝕃| A → |𝕃| A
  |map| : {A B : Set} → (A → B) → |𝕃| A → |𝕃| B
  _|::|_ : {A : Set} → A → |𝕃| A → |𝕃| A
  |[]| : {A : Set} → |𝕃| A


|null| : {A : Set} → |𝕃| A → 𝔹
|null| |[]| = tt
|null| _    = ff

|null≡| : {A : Set}(xs : |𝕃| A) → |null| xs ≡ tt → xs ≡ |[]| 
|null≡| (toRep x) ()
|null≡| (xs |++| xs₁) ()
|null≡| (|map| x xs) ()
|null≡| (x |::| xs) ()
|null≡| |[]| p = refl

⟦_⟧ : {A : Set} → |𝕃| A → 𝕃 A
⟦ toRep l ⟧ = l
⟦ xs |++| ys ⟧ = ⟦ xs ⟧ ++ ⟦ ys ⟧
⟦ |map| f xs ⟧ = map f ⟦ xs ⟧
⟦ x |::| xs ⟧ = x :: ⟦ xs ⟧
⟦ |[]| ⟧ = []


simstep : {A : Set} → |𝕃| A → |𝕃| A
simstep ((xs |++| ys) |++| zs) = xs |++| (ys |++| zs)
simstep ((x |::| xs) |++| ys)  = x |::| (xs |++| ys)
simstep (|[]| |++| xs)         = xs
simstep ((toRep list) |++| ys) with |null| ys
...                       | tt = toRep list
...                       | ff = (toRep list) |++| ys
simstep ((|map| f xs) |++| ys) with |null| ys
...                       | tt = |map| f xs
...                       | ff = (|map| f xs) |++| ys
simstep (|map| f (xs |++| ys)) = (|map| f xs) |++| (|map| f ys)
simstep (|map| f (toRep xs))   = toRep (map f xs)
simstep (|map| f (|map| g xs)) = |map| (f ∘ g) xs
simstep (|map| f (x |::| xs))  = (f x) |::| (|map| f xs)
simstep (|map| f |[]|)         = |[]|
simstep (toRep xs)             = toRep xs
simstep (x |::| xs)            = (x |::| xs)
simstep |[]|                   = |[]|

--++-homo : map f (xs ++ ys) ≡ map f xs ++ map f ys
simstep-sound : {A : Set} (xs : |𝕃| A) →
  ⟦ xs ⟧ ≡ ⟦ simstep xs ⟧
simstep-sound ((xs |++| ys) |++| zs) rewrite
    ++-assoc ⟦ xs ⟧ ⟦ ys ⟧ ⟦ zs ⟧
  = refl
simstep-sound ((x |::| xs) |++| ys)  = refl
simstep-sound (|[]| |++| xs)         = refl
simstep-sound ((toRep list) |++| ys) with inspect (|null| ys)
...                                  | tt with≡ p rewrite
                                         |null≡| ys p
                                       | ++[] list
                                       = refl
...                                  | ff with≡ p rewrite p = refl
simstep-sound ((|map| f xs) |++| ys) with inspect (|null| ys)
...                                  | tt with≡ p rewrite
                                         |null≡| ys p
                                       | ++[] (map f ⟦ xs ⟧)
                                       = refl
...                                  | ff with≡ p rewrite p = refl
simstep-sound (|map| f (xs |++| ys)) rewrite
    ++-homo ⟦ xs ⟧ ⟦ ys ⟧ f
  = refl 
simstep-sound (|map| f (toRep xs))   = refl 
simstep-sound (|map| f (|map| g xs)) rewrite
    sym (map-∘ f g ⟦ xs ⟧)
  = refl 
simstep-sound (|map| f (x |::| xs))  = refl 
simstep-sound (|map| f |[]|)         = refl 
simstep-sound (toRep xs)             = refl 
simstep-sound (x |::| xs)            = refl 
simstep-sound |[]|                   = refl 


sdstep : {A : Set} → |𝕃| A → |𝕃| A
sdstep (xs |++| ys) = simstep (sdstep xs |++| sdstep ys)
sdstep (|map| f xs) = simstep (|map| f (sdstep xs))
sdstep (x |::| xs) = simstep (x |::| (sdstep xs))
sdstep xs = xs

sdstep-sound : {A : Set} (xs : |𝕃| A) →
  ⟦ xs ⟧ ≡ ⟦ sdstep xs ⟧
sdstep-sound (toRep x) = refl
sdstep-sound (xs |++| ys) rewrite
    sdstep-sound xs
  | sdstep-sound ys
  | simstep-sound (sdstep xs |++| sdstep ys)
  = refl
sdstep-sound (|map| f xs) rewrite
    sdstep-sound xs
  | simstep-sound (|map| f (sdstep xs))
  = refl
sdstep-sound (x |::| xs) rewrite
    sdstep-sound xs
  | simstep-sound (x |::| (sdstep xs))
  = refl
sdstep-sound |[]| = refl

simplify : {A : Set} → |𝕃| A → ℕ → |𝕃| A
simplify xs 0 = xs
simplify xs (suc fuel) = sdstep (simplify xs fuel)

simplify-sound : {A : Set} (xs : |𝕃| A) (n : ℕ) →
  ⟦ xs ⟧ ≡ ⟦ simplify xs n ⟧
simplify-sound xs 0 = refl
simplify-sound xs (suc n) rewrite
    sym (sdstep-sound (simplify xs n))
  | simplify-sound xs n
  = refl

