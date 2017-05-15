open import Agda.Builtin.Coinduction using (∞; ♯_; ♭)
open import MyNats using (ℕ; suc; zero)
open import MyList using (_∘_)
open import Utils

{-
∞ = \inf
♭ = \b
♯ = \sharp

∞  : (A : Set) → Set       -- laziness set constructor
♯_ : {A : Set} → A → ∞ A   -- compiled as delay
♭  : {A : Set} → ∞ A → A   -- compiled as force

infix 1000 ♯_

data ∞ (A : Set) : Set where
  ♯_ : A → ∞ A

♭ : {A : Set} → ∞ A → A
♭ (♯ x) = x

-}

data ℕω : Set where
  ωzero : ℕω
  ωsuc : ∞ ℕω → ℕω

data Stream (A : Set) : Set where
  _::_ : A → ∞ (Stream A) → Stream A

infixr 5 _::_

-- Recursive stream functions

head : {A : Set} → Stream A → A
head (x :: xs) = x

tail : {A : Set} → Stream A → Stream A
tail (x :: xs) = ♭ xs

lookup : {A : Set} → ℕ → Stream A → A
lookup zero    (x :: xs) = x
lookup (suc n) (x :: xs) = lookup n (♭ xs)

--take : {A : Set} (n : ℕ) → Stream A → Vec A n
--take zero    xs       = []
--take (suc n) (x :: xs) = x :: take n (♭ xs)

drop : {A : Set} → ℕ → Stream A → Stream A
drop zero xs = xs
drop (suc n) (x :: xs) = drop n (♭ xs)

--Corecursive stream functions

repeat : {A : Set} → A → Stream A
repeat x = x :: ♯ repeat x

iterate : {A : Set} → (A → A) → A → Stream A
iterate f x = x :: ♯ iterate (f ∘ f) x

map : {A B : Set} → (A → B) → Stream A → Stream B
map f (x :: xs) = f x :: ♯ map f (♭ xs)

zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
zipWith z (x :: xs) (y :: ys) = z x y :: ♯ zipWith z (♭ xs) (♭ ys)


-- Relations

data _≈_ {A : Set} : Stream A → Stream A → Set where
  _::_ : (x : A) {xs ys : ∞ (Stream A)} → 
        ∞ (♭ xs ≈ ♭ ys) → x :: xs ≈ x :: ys

infix 4 _≈_


-- Proofs
≈-refl : {A : Set} {xs : Stream A} → xs ≈ xs
≈-refl {A} {x :: xs} = x :: ♯ ≈-refl

≈-sym : {A : Set} {xs ys : Stream A} → xs ≈ ys → ys ≈ xs
≈-sym = {!!}

≈-trans : {A : Set} {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans = {!!}

map-cong : {A B : Set} (f : A → B) {xs ys : Stream A} →
           xs ≈ ys → map f xs ≈ map f ys
map-cong = {!!}

elem-≡ : {A : Set} {xs ys : Stream A} → 
         xs ≈ ys → (n : ℕ) → lookup n xs ≡ lookup n ys
elem-≡ = {!!}

{-
Rec, a type which is analogous to the Rec type constructor used in
ΠΣ (see Altenkirch, Danielsson, Löh and Oury. ΠΣ: Dependent Types
without the Sugar. FLOPS 2010, LNCS 6009.)

data Rec {a} (A : ∞ (Set a)) : Set a where
  fold : (x : ♭ A) → Rec A

unfold : ∀ {a} {A : ∞ (Set a)} → Rec A → ♭ A
unfold (fold x) = x
-}
