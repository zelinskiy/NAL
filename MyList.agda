module MyList where

open import Agda.Builtin.Equality

open import MyNats
open import MyBool

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A

infixr 40 _::_

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixl 30 _++_

++-assoc : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → (ys : 𝕃 A) → (zs : 𝕃 A) →
                                            xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs rewrite ++-assoc xs ys zs = refl

length : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ
length [] = ℤ
length (x :: xs) = 𝕊 (length xs)

list0 : 𝕃 Set
list0 = ℕ :: 𝔹 :: 𝕃 (𝕃 𝔹) :: []

listℕ : 𝕃 ℕ
listℕ = 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: []

length-homo : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → (ys : 𝕃 A) →
                       length (xs ++ ys) ≡ length xs + length ys
length-homo [] ys = refl
length-homo (x :: xs) ys rewrite length-homo xs ys = refl

map : ∀ {ℓ} {A B : Set ℓ} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x :: xs) = (f x) :: map f xs

id : ∀ {ℓ} {A : Set ℓ} → (A → A)
id = λ x → x

map-preserve-length : ∀ {ℓ} {A B : Set ℓ} → (f : A → B) → (xs : 𝕃 A) →
                                                              length(map f xs) ≡ length xs
map-preserve-length f [] = refl
map-preserve-length f (x :: xs) rewrite map-preserve-length f xs = refl

_∘_ : {A : Set}{B : A → Set}{C : {x : A} → B x → Set}
    → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

map-id : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → map id xs ≡ xs
map-id [] = refl
map-id (x :: xs) rewrite map-id xs = refl

map-∘ : ∀ {A B C : Set} → (f : B → C) →  (g : A → B) → (xs : 𝕃 A) →
                                            map (f ∘ g) xs ≡ ((map f) ∘ (map g)) xs
map-∘ f g [] = refl
map-∘ f g (x :: xs) rewrite map-∘ f g xs = refl


reverse :  ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
reverse [] = []
reverse (x :: xs) = reverse xs ++ x :: []

++[] : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → xs ++ [] ≡ xs
++[]  [] = refl
++[]  (x :: xs) rewrite ++[] xs = refl

[]++ : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → [] ++ xs ≡ xs
[]++ xs = refl


reverse-contravariant : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → (ys : 𝕃 A) →
                                 reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-contravariant [] [] = refl
reverse-contravariant [] (y :: ys) rewrite
                      reverse-contravariant [] ys |
                      ++[] (reverse ys) |
                      ++[] (reverse ys ++ y :: [])
                      = refl
reverse-contravariant (x :: xs) [] rewrite
                      reverse-contravariant xs [] = refl
reverse-contravariant (x :: xs) (y :: ys) rewrite
                      reverse-contravariant xs (y :: ys) |
                      reverse-contravariant (x :: xs) (ys) |
                      ++-assoc (reverse ys ++ y :: []) (reverse xs) (x :: [])
                      = refl


2-reverse : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → reverse (reverse xs) ≡ xs
2-reverse [] = refl
2-reverse (x :: xs) rewrite
             2-reverse xs |
             reverse-contravariant (reverse xs) (x :: []) |
             2-reverse xs
             = refl

reverse-preserves-length : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A)
                                 → length (reverse xs) ≡ length xs
reverse-preserves-length [] = refl
reverse-preserves-length (x :: xs) rewrite
                         reverse-preserves-length xs |
                         length-homo (reverse xs) (x :: []) |
                         reverse-preserves-length xs |
                         +comm (length xs) 1
                         = refl
