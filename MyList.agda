module MyList where

open import Utils

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

length-homo : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → (ys : 𝕃 A) →
                       length (xs ++ ys) ≡ length xs + length ys
length-homo [] ys = refl
length-homo (x :: xs) ys rewrite length-homo xs ys = refl

map : ∀ {ℓ} {A B : Set ℓ} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x :: xs) = (f x) :: map f xs

filter : ∀ {ℓ} {A : Set ℓ} → (f : A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter f (x :: xs) with f x
... | tt = x :: filter f xs
... | ff = filter f xs

map-preserve-length : ∀ {ℓ} {A B : Set ℓ} → (f : A → B) → (xs : 𝕃 A) →
                                         length(map f xs) ≡ length xs
map-preserve-length f [] = refl
map-preserve-length f (x :: xs) rewrite map-preserve-length f xs = refl

_∘_ : {A : Set}{B : A → Set}{C : {x : A} → B x → Set}
    → (f : {x : A} → (y : B x) → C y) → (g : (x : A) → B x) → ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

map-id : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → map (λ x → x) xs ≡ xs
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


--≤-suc : ∀ (n : ℕ) → n ≤ suc n ≡ tt
--≤-trans : ∀ {x y z : ℕ} → x ≤ y ≡ tt → y ≤ z ≡ tt → x ≤ z ≡ tt

filter-less : ∀ {ℓ} {A : Set ℓ} → (p : A → 𝔹) → (xs : 𝕃 A) →
            length (filter p xs) ≤ length xs ≡ tt
filter-less p [] = refl
filter-less p (x :: xs) with p x
... | tt = filter-less p xs
... | ff = ≤-trans {length (filter p xs)} (filter-less p xs) (≤-suc (length xs))


filter-idemp : ∀ {ℓ} {A : Set ℓ} (p : A → 𝔹) (xs : 𝕃 A) → (filter p (filter p xs)) ≡ (filter p xs)
filter-idemp p [] = refl
filter-idemp p (x :: xs) with inspect (p x)
filter-idemp p (x :: xs) | tt with≡ p' rewrite p' | p' | p' | filter-idemp p xs = refl
filter-idemp p (x :: xs) | ff with≡ p' rewrite p' | p' | filter-idemp p xs = refl

infixr 40 _∈ₙ_

_∈ₙ_ : ℕ → 𝕃 ℕ → 𝔹
x ∈ₙ [] = ff
x ∈ₙ (y :: ys) = if (x == y) then tt else (x ∈ₙ ys)

_⊆ₙ_ : 𝕃 ℕ → 𝕃 ℕ → 𝔹
[] ⊆ₙ ys = tt
(x :: xs) ⊆ₙ ys = if (x ∈ₙ ys) then xs ⊆ₙ ys else ff

