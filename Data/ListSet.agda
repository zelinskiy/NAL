module NAL.Data.ListSet where

open import NAL.Data.List
open import NAL.Data.Nats
open import NAL.Data.Bool
open import NAL.Data.Eq

open import NAL.Utils.Core

data ListSet {ℓ}(A : Set ℓ){{_ : Eq A}} : Set ℓ where
  mkLS : 𝕃 A → ListSet A

fromList : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → 𝕃 A → ListSet A
fromList xs = mkLS (nub xs)

fromSet : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → 𝕃 A
fromSet (mkLS xs) = xs

singletonSet : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → A → ListSet A
singletonSet x = mkLS [ x ]

∅ : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A
∅ = mkLS []

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

filterttLemma : ∀{ℓ}{T : Set ℓ}{xs : 𝕃 T} → filter (λ z → tt) xs ≡ xs
filterttLemma {xs = []} = refl
filterttLemma {xs = x :: xs} = cong (x ::_) filterttLemma

postulate
  ∪-projL : ∀{ℓ}{T : Set ℓ}{{eqT : Eq T}}{A B : ListSet T}{x : T} → x ∈? (A ∪ B) ≡ ff → x ∈? A ≡ ff
  ∪-projR : ∀{ℓ}{T : Set ℓ}{{eqT : Eq T}}{A B : ListSet T}{x : T} → x ∈? (A ∪ B) ≡ ff → x ∈? B ≡ ff
{-
∪-projL : ∀{ℓ}{T : Set ℓ}{{eqT : Eq T}}{A B : ListSet T}{x : T} →
  x ∈? (A ∪ B) ≡ ff →
  x ∈? A ≡ ff
∪-projL {A = mkLS []} {mkLS []} p = p
∪-projL {A = mkLS []} {mkLS (b :: bs)}{x} p with x is b
∪-projL {A = mkLS []} {mkLS (b :: bs)}{x} p | tt = refl
∪-projL {A = mkLS []} {mkLS (b :: bs)}{x} p | ff = refl
∪-projL {A = mkLS (a :: as)} {mkLS []}{x} p with x is a
∪-projL {A = mkLS (a :: as)} {mkLS []}{x} p | tt = 𝔹-contra (sym p)
∪-projL {A = mkLS (a :: as)} {mkLS []}{x} p | ff rewrite ++[] (filter (λ z → tt) as) | filterttLemma {xs = as} = p
∪-projL {A = mkLS (a :: as)} {mkLS  bs} {x} p with inspect (x is a)
... | tt with≡ ()
... | ff with≡ q rewrite q | ∪-projL {A = mkLS as} {mkLS bs} {x} {!!} = refl
-}
_∩_ : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → ListSet A → ListSet A → ListSet A
xs ∩ ys = mkLS (filter (λ e → e ∈? xs ∧ e ∈? ys) (fromSet xs))

postulate
  thm1 : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}}{a b : ListSet A} →
    (a ⊆? b) ∧ (b ⊆? a) ≡ tt →
    a ≡ b

{-
thm1 {a = mkLS []} {mkLS []} p = refl
thm1 {a = mkLS []} {mkLS (b :: bs)} p = {!!}
thm1 {a = mkLS (a :: as)} {mkLS []} p = {!!}
thm1 {a = mkLS (a :: as)} {mkLS (b :: bs)} p = {!!}
-}
instance
  EqListSet : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → Eq (ListSet A)
  EqListSet = record { _is_ = λ A B → (A ⊆? B) ∧ (B ⊆? A)}

-- record {_is_ = λ A B → (A ⊆? B) ∧ (B ⊆? A)}
