module NAL.Data.ListSet where

open import NAL.Data.List
open import NAL.Data.Nats
open import NAL.Data.Bool
open import NAL.Data.Eq

data ListSet {ℓ}(A : Set ℓ){{_ : Eq A}} : Set ℓ where
  mkLS : 𝕃 A → ListSet A

fromList : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → 𝕃 A → ListSet A
fromList xs = mkLS (nub xs)

fromSet : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → 𝕃 A
fromSet (mkLS xs) = xs

singletonSet : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → A → ListSet A
singletonSet x = mkLS [ x ]

ø : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A
ø = mkLS []

card : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → ℕ
card (mkLS s) = length s 

_∈?_ : ∀{ℓ}{A : Set ℓ}{{co : Eq A}} → A → ListSet A → 𝔹
x ∈? (mkLS []) = ff
x ∈? (mkLS (y :: ys)) = if x is y  then tt else (x ∈? (mkLS ys))

_⊆?_ : ∀{ℓ}{A : Set ℓ}{{co : Eq A}} → ListSet A → ListSet A → 𝔹
(mkLS A) ⊆? B = and (map (_∈? B) A)


_─_ : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → ListSet A → ListSet A
(mkLS xs) ─ ys = mkLS (filter (λ x → ¬ (x ∈? ys)) xs)

_∪_ : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → ListSet A → ListSet A
xs ∪ ys = mkLS ((fromSet (xs ─ ys)) ++ (fromSet ys))

_∩_ : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → ListSet A → ListSet A
xs ∩ ys = mkLS (filter (λ e → e ∈? xs ∧ e ∈? ys) (fromSet xs))

instance
  EqListSet : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → Eq (ListSet A)
  EqListSet = record {_is_ = λ A B → (A ⊆? B) ∧ (B ⊆? A)}
