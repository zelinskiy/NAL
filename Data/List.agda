module NAL.Data.List where

open import NAL.Utils.Core
open import NAL.Data.Nats
open import NAL.Data.Bool
open import NAL.Data.Pair
open import NAL.Data.Eq


open import NAL.Utils.Function


data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A


{-# BUILTIN LIST 𝕃 #-}
{-# BUILTIN CONS _::_ #-}
{-# BUILTIN NIL [] #-}

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
length [] = zero
length (x :: xs) = suc (length xs)

length-homo : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → (ys : 𝕃 A) →
                       length (xs ++ ys) ≡ length xs + length ys
length-homo [] ys = refl
length-homo (x :: xs) ys rewrite length-homo xs ys = refl

map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → 𝕃 A → 𝕃 B
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


map-id : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → map (λ x → x) xs ≡ xs
map-id [] = refl
map-id (x :: xs) rewrite map-id xs = refl

map-∘ : ∀ {ℓ} {A B C : Set ℓ} → (f : B → C) →  (g : A → B) → (xs : 𝕃 A) →
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

++-homo : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  (xs ys : 𝕃 A) (f : A → B) →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
++-homo [] [] f = refl
++-homo [] (y :: ys) f = refl
++-homo (x :: xs) [] f rewrite
  ++[] (x :: xs) |
  ++-homo xs [] f
  = refl
++-homo (x :: xs) (y :: ys) f rewrite
  ++-homo xs ys f |
  ++-homo xs (y :: ys) f
  = refl



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



filter-step-lemma : ∀ {ℓ} {A : Set ℓ} →
  (x : A) (xs : 𝕃 A) (p : A → 𝔹) (q : p x ≡ tt) →
  filter p (x :: xs) ≡ x :: (filter p xs)
filter-step-lemma x xs p q rewrite q = refl

filter-idemp : ∀ {ℓ} {A : Set ℓ} (p : A → 𝔹) (xs : 𝕃 A) →
  (filter p (filter p xs)) ≡ (filter p xs)
filter-idemp p [] = refl
filter-idemp p (x :: xs) with inspect (p x)
filter-idemp p (x :: xs) | tt with≡ p' rewrite
  filter-step-lemma x xs p p' |
  filter-step-lemma x (filter p xs) p p' |
  filter-idemp p xs
  = refl  
filter-idemp p (x :: xs) | ff with≡ p' rewrite
  p' |
  p' |
  filter-idemp p xs
  = refl

infixr 40 _∈ₙ_

_∈ₙ_ : ℕ → 𝕃 ℕ → 𝔹
x ∈ₙ [] = ff
x ∈ₙ (y :: ys) = if (x == y) then tt else (x ∈ₙ ys)

data _∈_ {A : Set}(x : A) : 𝕃 A → Set where
  hd : ∀ {xs} → x ∈ x :: xs
  tl : ∀ {y xs} → x ∈ xs → x ∈ y :: xs

{-
_⊆_ : ∀ {A : Set}(xs ys : 𝕃 A) → Set
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys
-}

data _⊆_ {A : Set} : 𝕃 A → 𝕃 A → Set where
  _subset_ : ∀ {x xs ys} → x ∈ xs → x ∈ ys → xs ⊆ ys


THM2 : 1 :: 2 :: [] ⊆ 3 :: 2 :: 1 :: []
THM2 = tl hd subset tl hd

zipWith : ∀ {ℓ} → ∀ {A B C : Set ℓ } → (f : A → B → C) → (𝕃 A) → (𝕃 B) → 𝕃 C
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

zipLists : ∀ {ℓ} → ∀ {A B : Set ℓ} → (𝕃 A) → (𝕃 B) → 𝕃 ⟪ A , B ⟫
zipLists = zipWith ⟨_,_⟩


foldr : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}{B : Set ℓ₂} → (A → B → B) → B → 𝕃 A → B
foldr f i [] = i
foldr f i (x :: xs) = f x (foldr f i xs)

concat : ∀ {ℓ} {A : Set ℓ} → 𝕃 (𝕃 A) → 𝕃 A
concat = foldr _++_ [] 

singleton : ∀ {ℓ} {A : Set ℓ} → A → 𝕃 A
singleton x = x :: []

[_] : ∀ {ℓ} {A : Set ℓ} → A → 𝕃 A
[ x ] = singleton x

concat-map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
  (xss : 𝕃 (𝕃 A)) (f : A → B) →
  concat (map (map f) xss) ≡ map f (concat xss)
concat-map [] f = refl
concat-map (xs :: xss) f rewrite
  concat-map xss f |
  sym (++-homo xs (concat xss) f)
  = refl

index : ∀ {A} {x : A} {xs} → x ∈ xs → ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : 𝕃 A) : ℕ -> Set where
  inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : ℕ) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : 𝕃 A)(n : ℕ) -> Lookup xs n
[] ! n = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n with xs ! n
(x :: xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x :: xs) ! suc .(length xs + n) | outside n = outside n


∈-relax-right : ∀ {A} {x : A} {xs ys} → x ∈ xs → x ∈ (xs ++ ys)
∈-relax-right hd = hd
∈-relax-right (tl y) = tl (∈-relax-right y)

∈-relax-left : ∀ {A} {y : A} xs {ys} → y ∈ ys → y ∈ (xs ++ ys)
∈-relax-left [] p = p
∈-relax-left (_ :: xs) p = tl (∈-relax-left xs p)




nubBy : ∀{ℓ}{A : Set ℓ} → (A → A → 𝔹) → 𝕃 A → 𝕃 A
nubBy p xs = nub0 p xs (length xs)
  where
    nub0 : ∀{ℓ}{A : Set ℓ}→ (A → A → 𝔹) → 𝕃 A → ℕ → 𝕃 A
    nub0 p (x :: xs) (suc fuel) = x :: nub0 p (filter (λ y → ¬ (p x y)) xs) fuel
    nub0 p [] (suc fuel) = []
    nub0 p _ 0 = []

nub : ∀{ℓ}{A : Set ℓ}{{_ : Eq A}} → 𝕃 A → 𝕃 A
nub xs = nubBy _is_ xs

range : ℕ → ℕ → 𝕃 ℕ
range x y = reverse (y :: h x y)
  where
    h : ℕ → ℕ → 𝕃 ℕ
    h x (suc y) = if x < y then y :: h x y else [ y ]
    h x 0 = []

[_-_] : ℕ → ℕ → 𝕃 ℕ
[ a - b ] = range a b

all : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝔹
all f = foldr (λ x y → y ∧ f x) tt

any : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝔹
any f = foldr (λ x y → y ∨ f x) ff

and : 𝕃 𝔹 → 𝔹
and xs = all (λ x → x) xs

shift : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
shift _ [] = []
shift 0 xs = xs
shift (suc n) (x :: xs) = shift n (xs ++ [ x ])


comb : ∀{ℓ}{A : Set ℓ} → ℕ -> 𝕃 A → 𝕃 (𝕃 A)
comb 0 _      = [] :: []
comb _ []     = []
comb (suc m) (x :: xs) = map (λ ys → x :: ys) (comb m xs) ++ comb (suc m) xs

_×_ : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂} → 𝕃 A → 𝕃 B → 𝕃 ⟪ A , B ⟫
[] × _ = []
_ × [] = []
(x :: xs) × ys = map (⟨_,_⟩ x) ys ++ (xs × ys)

exchange : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
exchange 0 (x :: y :: xs) = (y :: x :: xs)
exchange (suc n) (x :: xs) = x :: exchange n xs
exchange _ [] = []
exchange 0 xs = xs

dropLast : ∀{ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
dropLast [] = []
dropLast (x :: []) = []
dropLast (x :: xs) = x :: dropLast xs

dropFirst : ∀{ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A
dropFirst [] = []
dropFirst (x :: xs) = xs
