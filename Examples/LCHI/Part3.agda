module NAL.Examples.LCHI.Part3 where

open import NAL.Data.Nats
open import NAL.Data.List
open import NAL.Data.ListSet
open import NAL.Data.Eq
open import NAL.Data.Bool
open import NAL.Data.Pair
open import NAL.Data.Triple
open import NAL.Data.String

open import NAL.Utils.Core
open import NAL.Utils.Dependent hiding (Π)

infixl 10 _∷_
infixr 50 ƛ_!_
infixl 80 _$_
infixl 5 _⊢_∷_
infixr 30 _⇒_

data Π : Set where
  tvar : String → Π
  _⇒_ : Π → Π → Π

instance
  EqΠ : Eq Π
  EqΠ = record {_is_ = eq}
    where
      eq : Π → Π → 𝔹
      eq (tvar α) (tvar β) = α is β
      eq (α₁ ⇒ β₁) (α₂ ⇒ β₂) = (eq α₁ α₂) ∧ (eq β₁ β₂)
      eq _ _ = ff

mutual
  data Binding : Set where
     _∷_ : Λ → Π → Binding

  data Λ : Set where
     var : String → Λ
     _$_ : Λ → Λ → Λ
     ƛ_!_ : Λ → Λ → Λ

typeof :  Binding → Π
typeof (_ ∷ τ) = τ

Context = 𝕃 Binding

dom : Context → 𝕃 String
dom [] = []
dom (((var x) ∷ t) :: bs) = x :: dom bs
dom (_ :: bs) = dom bs

ran : Context → 𝕃 Π
ran Γ = nub (map (λ { (x ∷ τ) → τ}) Γ)

exchange : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
exchange 0 (x :: y :: xs) = (y :: x :: xs)
exchange (suc n) (x :: xs) = x :: exchange n xs
exchange _ [] = []
exchange 0 xs = xs

data _⊢_∷_ : Context → Λ → Π → Set where
  Ax : ∀ {Γ x τ} → (var x ∷ τ) :: Γ ⊢ var x ∷ τ -- x ∉ dom Γ
  Abs : ∀ {Γ x τ M σ} → (x ∷ σ) :: Γ ⊢ M ∷ τ → Γ ⊢ ƛ x ! M ∷ σ ⇒ τ -- x ∉ dom Γ
  App : ∀ {Γ τ M σ N} → Γ ⊢ M ∷ σ ⇒ τ → Γ ⊢ N ∷ σ → Γ ⊢ (M $ N) ∷ τ
  Exchange : ∀ {Γ x τ} → (n : ℕ) → exchange n Γ ⊢ x ∷ τ → Γ ⊢ x ∷ τ
  



STLC = mkTriple Λ Π _⊢_∷_

Ex1 : [] ⊢ ƛ var "x" ! var "x" ∷ tvar "σ" ⇒ tvar "σ"
Ex1 = Abs Ax

Ex2 : [] ⊢ ƛ var "x" ! ƛ var "y" ! var "x" ∷ tvar "σ" ⇒ tvar "τ" ⇒ tvar "σ"
Ex2 = Abs (Abs (Exchange 0 Ax))

Ex3 : [] ⊢ ƛ var "x" ! ƛ var "y" ! ƛ var "z" ! var "x" $ var "z" $ (var "y" $ var "z")
  ∷ (tvar "σ" ⇒ tvar "τ" ⇒ tvar "ρ") ⇒ (tvar "σ" ⇒ tvar "τ") ⇒ tvar "σ" ⇒ tvar "ρ"
Ex3 = Abs(
  Abs(Abs(
    App{σ = tvar "τ"} (
      App{σ =  tvar "σ"} (
        Exchange 1 (
          Exchange 0
            Ax))
        Ax)
     (App{σ =  tvar "σ"}
       (Exchange 0 Ax)
       Ax))))

FV' : Λ → ListSet String
FV' (var x) = singletonSet x
FV' (ƛ x ! P) = FV' P ─  FV' x
FV' (P $ Q) = FV' P ∪ FV' Q

FV : Λ → 𝕃 String
FV t = fromSet (FV' t)
    


postulate
  FVlemma1 : ∀ {Γ Γ′ M σ} → Γ ⊢ M ∷ σ → Γ ⊆ Γ′ → Γ′ ⊢ M ∷ σ
  FVlemma2 : ∀{M Γ σ} → Γ ⊢ M ∷ σ → FV M ⊆ dom Γ
  FVlemma3 : ∀{Γ Γ′ M σ} → Γ ⊢ M ∷ σ → dom Γ′ ≡ FV M → Γ′ ⊆ Γ → Γ′ ⊢ M ∷ σ

postulate
  GenerationLemma1 : ∀ {Γ x σ} → Γ ⊢ x ∷ σ → (x ∷ σ) ∈ Γ
  GenerationLemma2 : ∀{Γ M N σ} → Γ ⊢ M $ N ∷ σ →
    Σ Π (λ τ → ⟪ (Γ ⊢ M ∷ τ ⇒ σ) , (Γ ⊢ N ∷ τ) ⟫)
  GenerationLemma3 : ∀ {Γ M x σ} → Γ ⊢ (ƛ x ! M) ∷ σ →
    Σ ⟪ Π , Π ⟫ (λ {⟨ τ , ρ ⟩ → ⟪ ((x ∷ τ) :: Γ ⊢ M ∷ ρ) , (σ ≡ τ ⇒ ρ) ⟫})

doubleEx : ∀{ℓ}{A : Set ℓ}{n : ℕ}{xs : 𝕃 A} → (exchange n (exchange n xs)) ≡ xs
doubleEx {n = zero} {[]} = refl
doubleEx {n = zero} {x :: y :: xs} = refl
doubleEx {n = zero} {x :: []} = refl
doubleEx {n = suc n} {[]} = refl
doubleEx {n = suc n} {x :: xs} rewrite doubleEx {n = n} {xs} = refl

doubleExchange : ∀{Γ x τ n} → Γ ⊢ x ∷ τ → exchange n (exchange n Γ) ⊢ x ∷ τ
doubleExchange {Γ} {x} {τ} {n} p rewrite doubleEx {n = n} {xs = Γ} = p

doubleExchangeR : ∀{Γ x τ n} → exchange n (exchange n Γ) ⊢ x ∷ τ →  Γ ⊢ x ∷ τ
doubleExchangeR {Γ} {x} {τ} {n} p rewrite doubleEx {n = n} {xs = Γ} = p

ExchangeRev : ∀ {Γ x τ n} → Γ ⊢ x ∷ τ → exchange n Γ ⊢ x ∷ τ
ExchangeRev {Γ} {x} {τ} {n} p = Exchange n (doubleExchange {n = n} p)
{-
GenerationLemma11 : ∀ {Γ x σ} → Γ ⊢ var x ∷ σ → (var x ∷ σ) ∈ Γ
GenerationLemma11 Ax = hd
GenerationLemma11 {Γ} {x} {σ} (Exchange n p) = {!!}
-}

newVar : String → String → 𝕃 String → String
newVar x y vs = primStringAppend x "'" 

infixl 100 _[_:=_]
{-# TERMINATING #-}
_[_:=_] : Λ → String → Λ → Λ
var x [ y := N ] with x is y
... | tt = N
... | ff = var x
(P $ Q) [ x := N ] = (P [ x := N ] $ Q [ x := N ]) 
(ƛ (var y) ! P)[ x := N ] with x is y
(ƛ (var y) ! P)[ x := N ] | tt = ƛ (var x) ! P
(ƛ (var y) ! P)[ x := N ] | ff with ¬ (x ∈? FV' N) ∨  ¬ (x ∈? FV' P)
(ƛ (var y) ! P)[ x := N ] | ff | tt = (ƛ var y ! P [ x := N ])
(ƛ (var y) ! P)[ x := N ] | ff | ff with x ∈? FV' N ∧ y ∈? FV' P
(ƛ (var y) ! P)[ x := N ] | ff | ff | tt = ƛ var y ! P [ y := var z ] [ x := N ]
  where z = newVar y x [] --Problematic call here
(ƛ (var y) ! P)[ x := N ] | ff | ff | ff = (ƛ var y ! P)
(ƛ wtf ! P)[ x := N ] = ƛ wtf ! P [ x := N ]

_[_≔_] : Π → String → Π → Π
(tvar β) [ α ≔ τ ] with α is β
... | tt = τ
... | ff = tvar β
(σ₁ ⇒ σ₂) [ α ≔ τ ] = (σ₁ [ α ≔ τ ]) ⇒ (σ₂ [ α ≔ τ ])

_[_≔ᵣ_] : Context → String → Π → Context
((x ∷ (tvar σ)) :: Γ) [ α ≔ᵣ τ ] = (if σ is α then x ∷ τ else (x ∷ (tvar σ))) :: (Γ [ α ≔ᵣ τ ])
(b :: Γ) [ α ≔ᵣ τ ] = b :: (Γ [ α ≔ᵣ τ ])
[] [ _ ≔ᵣ _ ] = []

postulate
  SubLemma1 : ∀{Γ M σ α τ} → Γ ⊢ M ∷ σ → Γ [ α ≔ᵣ τ ] ⊢ M ∷ (σ [ α ≔ τ ])
  SubLemma2 : ∀{Γ M N σ τ x} → (var x ∷ τ) :: Γ ⊢ M ∷ σ → Γ ⊢ N ∷ τ → Γ ⊢ (_[_:=_] M x N) ∷ σ

reduce : Λ → Λ
reduce ((ƛ var x ! M) $ N) = M [ x := N ]
reduce M = M

reduceN : {n : ℕ} → Λ → Λ
reduceN {0} M = M
reduceN{suc n} M = reduceN {n} (reduce M)

--TODO : α-equivalence

_↠β_ : Λ → Λ → Set
M ↠β N = {n : ℕ} → reduceN {n} M ≡ N

_→β_ : Λ → Λ → Set
M →β N = reduce M ≡ N


postulate
  SubjectReduction : ∀ {Γ M N σ} → Γ ⊢ M ∷ σ → M →β N → Γ ⊢ N ∷ σ
  SubjectExpansion : ∀ {Γ M N σ} → Γ ⊢ M ∷ σ → M ↠β N → Γ ⊢ N ∷ σ
  ChurchRosser : ∀{Γ M N N′ σ} → Γ ⊢ M ∷ σ → M ↠β N → M ↠β N′ →
    Σ Λ (λ L → ⟪ ⟪ N ↠β L , N′ ↠β L ⟫ , Γ ⊢ L ∷ σ ⟫)

l1 : ∀{M N} → _→β_ M N → reduce M ≡ N
l1 {M} {N} p = p

l2 : ∀{x M N} → reduce ((ƛ var x ! M) $ N) ≡ M [ x := N ]
l2 = refl


