module NAL.Examples.MLTT where

id : {A : Set} → A → A
id = λ x → x

data ⊥ : Set where

record ⊤ : Set where
  constructor ⊤-cons

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

depfun : ℕ → Set
depfun zero = ⊥
depfun _      = ⊤

record _∧_ (A : Set) (B : Set) : Set where
  constructor _×_
  field
    pr₁ : A
    pr₂ : B

curry : {A B C : Set} → (A ∧ B → C) → A → B → C
curry f a b = f (a × b)

uncurry : {A B C : Set} → (A → B → C) → A ∧ B → C
uncurry f (a × b) = f a b

record _∨_ (A : Set) (B : Set) : Set where
  constructor _+_
  field
    in₁ : A
    in₂ : B

record _⇒_ (A : Set) (B : Set) : Set where
  constructor _↦_


record Σ (A : Set) (P : A → Set) : Set where  
  constructor Σ_,_
  field
    π₁ : A       
    π₂ : P (π₁)
    
open Σ public

Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

ΠΣ : {A : Set} {B : A → Set} → Π A B → (a : A) → Σ A B
ΠΣ f x = Σ x , f x

--Martin-Lof Id type
data _≡_ {A : Set} (a : A) : A → Set where
  refl :  a ≡ a

{-
In Martin-Lof's papers appeared as:
data Id (A : Set) : A → A → Set where
  refl : {a : A} → Id A a a
-}

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl  = refl

cong : {A : Set} → {a b : A} → {B : Set} → {f : A → B} → a ≡ b → (f a) ≡ (f b)
cong refl = refl


data R {A B : Set} (a : A) (b : B) : Set where

--Axiom of Choice!
ac : {A B : Set} →
  Π A (λ a → Σ B (λ b → R a b ) ) →
  Σ (A → B) (λ f → (Π A (λ a → R a (f a))))
ac g = Σ (λ a → π₁ (g a)) , (λ a → π₂ (g a))

--Even without type levels ○ looks scary
_○_ : {A : Set} {B : A → Set} {C : (a : A) → (B a → Set)} →
      (f : {a : A} → Π (B a) (C a)) → (g : Π A B) → Π A (λ a → C a (g a))
f ○ g = λ x → f (g x)

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

curry-uncurry : {A B C : Set} → (f : (A ∧ B) → C) → uncurry (curry f) ≡ f
curry-uncurry f = refl

uncurry-curry : {A B C : Set} → (f : A → B → C) → curry (uncurry f) ≡ f
uncurry-curry f = refl


-- J operator
J : {A : Set} →
  {a b : A} →
  {C : (x y : A) → (z : x ≡ y) → Set} →
   ({x : A} → C x x refl) →
   (c : a ≡ b) →
   C a b c
J d refl = d

--Легендарный редуктор и популярный индуктор
recNat : (A : Set) → A → (ℕ → A → A) → ℕ → A
recNat A x f zero = x
recNat A x f (suc n) = f n (recNat A x f n)

indNat : (C : ℕ → Set) → C zero → ((x : ℕ) → C x → C (suc x)) → Π ℕ C
indNat C c₀ c₁ zero = c₀
indNat C c₀ f (suc n) = f n (indNat C c₀ f n)


