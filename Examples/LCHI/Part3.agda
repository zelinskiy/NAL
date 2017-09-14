module NAL.Examples.LCHI.Part3 where

open import NAL.Data.Nats
open import NAL.Data.List
open import NAL.Data.ListSet
open import NAL.Data.Eq
open import NAL.Data.Bool
open import NAL.Data.Pair
open import NAL.Data.Triple
open import NAL.Data.String
open import NAL.Data.Maybe

open import NAL.Utils.Core
open import NAL.Utils.Dependent hiding (Π)

infix 10 _∷_
infixr 50 ƛ_!_
infixl 80 _$_
infix 5 _⊢_∷_
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
     _∷_ : String → Π → Binding

  data Λ : Set where
     var : String → Λ
     _$_ : Λ → Λ → Λ
     ƛ_!_ : String → Λ → Λ

typeof :  Binding → Π
typeof (_ ∷ τ) = τ

Context = 𝕃 Binding

dom : Context → 𝕃 String
dom [] = []
dom ((x ∷ t) :: bs) = x :: dom bs


ran : Context → 𝕃 Π
ran Γ = map (λ { (x ∷ τ) → τ}) Γ



data _⊢_∷_ : Context → Λ → Π → Set where
  Ax : ∀ {Γ x τ} → (x ∷ τ) :: Γ ⊢ var x ∷ τ -- x ∉ dom Γ
  Abs : ∀ {Γ x τ M σ} → (x ∷ σ) :: Γ ⊢ M ∷ τ → Γ ⊢ ƛ x ! M ∷ σ ⇒ τ -- x ∉ dom Γ
  App : ∀ {Γ τ M σ N} → Γ ⊢ M ∷ σ ⇒ τ → Γ ⊢ N ∷ σ → Γ ⊢ (M $ N) ∷ τ

postulate Exchange : ∀ {Γ x τ} → (n : ℕ) → exchange n Γ ⊢ x ∷ τ → Γ ⊢ x ∷ τ
postulate
  Contract : ∀ {Γ x τ q ψ} → (x ∷ τ) :: (x ∷ τ) :: Γ ⊢ q ∷ ψ → (x ∷ τ) :: Γ ⊢ q ∷ ψ


height : ∀{Γ M τ} → Γ ⊢ M ∷ τ → ℕ
height Ax = 1
height (Abs p) = suc (height p)
height (App p q) = suc (maxₙ (height p) (height q))

STLC = mkTriple Λ Π _⊢_∷_

Ex1 : [] ⊢ ƛ "x" ! var "x" ∷ tvar "σ" ⇒ tvar "σ"
Ex1 = Abs Ax


Ex2 : [] ⊢ ƛ "x" ! ƛ "y" ! var "x" ∷ tvar "σ" ⇒ tvar "τ" ⇒ tvar "σ"
Ex2 = Abs (Abs (Exchange 0 Ax))

Ex3 : [] ⊢ ƛ "x" ! ƛ "y" ! ƛ "z" ! var "x" $ var "z" $ (var "y" $ var "z")
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
FV' (ƛ x ! P) = FV' P ─  singletonSet x
FV' (P $ Q) = FV' P ∪ FV' Q

FV : Λ → 𝕃 String
FV t = fromSet (FV' t)
    


postulate
  FVlemma1 : ∀ {Γ Γ′ M σ} → Γ ⊢ M ∷ σ → Γ ⊆ Γ′ → Γ′ ⊢ M ∷ σ
  FVlemma2 : ∀{M Γ σ} → Γ ⊢ M ∷ σ → FV M ⊆ dom Γ
  FVlemma3 : ∀{Γ Γ′ M σ} → Γ ⊢ M ∷ σ → dom Γ′ ≡ FV M → Γ′ ⊆ Γ → Γ′ ⊢ M ∷ σ

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

GenerationLemma1 : ∀ {Γ x σ} → Γ ⊢ var x ∷ σ → (x ∷ σ) ∈ Γ
GenerationLemma1 Ax = hd

GenerationLemma2 : ∀{Γ M N σ} → Γ ⊢ M $ N ∷ σ →
    Σ Π (λ τ → ⟪ (Γ ⊢ M ∷ τ ⇒ σ) , (Γ ⊢ N ∷ τ) ⟫)
GenerationLemma2 (App {σ = σ'} p q) = σ' , ⟨ p , q ⟩

GenerationLemma3 : ∀ {Γ M x σ} → Γ ⊢ (ƛ x ! M) ∷ σ →
  Σ ⟪ Π , Π ⟫ (λ {⟨ τ , ρ ⟩ → ⟪ ((x ∷ τ) :: Γ ⊢ M ∷ ρ) , (σ ≡ τ ⇒ ρ) ⟫})
GenerationLemma3  (Abs {τ = ρ}{σ = τ} p) = ⟨ τ , ρ ⟩ , ⟨ p , refl ⟩

newVar : String → String
newVar x = primStringAppend x "'" 

infixl 100 _[_:=_]
{-# TERMINATING #-}
_[_:=_] : Λ → String → Λ → Λ
var x [ y := N ] with x is y
... | tt = N
... | ff = var x
(P $ Q) [ x := N ] = (P [ x := N ] $ Q [ x := N ]) 
(ƛ y ! P)[ x := N ] with x is y
(ƛ y ! P)[ x := N ] | tt = ƛ x ! P
(ƛ y ! P)[ x := N ] | ff with ¬ (x ∈? FV' N) ∨  ¬ (x ∈? FV' P)
(ƛ y ! P)[ x := N ] | ff | tt = (ƛ y ! P [ x := N ])
(ƛ y ! P)[ x := N ] | ff | ff with x ∈? FV' N ∧ y ∈? FV' P
(ƛ y ! P)[ x := N ] | ff | ff | tt = ƛ y ! P [ y := var z ] [ x := N ]
  where z = newVar y --Problematic call here
(ƛ y ! P)[ x := N ] | ff | ff | ff = (ƛ y ! P)

_[_≔_] : Π → String → Π → Π
(tvar β) [ α ≔ τ ] with α is β
... | tt = τ
... | ff = tvar β
(σ₁ ⇒ σ₂) [ α ≔ τ ] = (σ₁ [ α ≔ τ ]) ⇒ (σ₂ [ α ≔ τ ])

_[_≔ᵣ_] : Context → String → Π → Context
((x ∷ σ) :: Γ) [ α ≔ᵣ τ ] = (x ∷ (σ [ α ≔ τ ])) :: (Γ [ α ≔ᵣ τ ])
[] [ _ ≔ᵣ _ ] = []

eq=>≡ : ∀{σ τ : Π} → σ is τ ≡ tt → σ ≡ τ
eq=>≡ {tvar x} {tvar y} p with inspect (x is y)
eq=>≡ {tvar x} {tvar y} p | tt with≡ q rewrite Strings≡ {x} {y} q = refl
eq=>≡ {tvar x} {tvar y} p | ff with≡ q rewrite q = 𝔹-contra p
eq=>≡ {tvar x} {τ ⇒ τ₁} ()
eq=>≡ {σ ⇒ σ₁} {tvar x} ()
eq=>≡ {σ ⇒ σ'} {τ ⇒ τ'} p rewrite eq=>≡ {σ} {τ} (a∧b→a p) | eq=>≡ {σ'} {τ'} (a∧b→b p) = refl 


postulate
  SubLemma2 : ∀{Γ M N σ τ x} → (x ∷ τ) :: Γ ⊢ M ∷ σ → Γ ⊢ N ∷ τ → Γ ⊢ (_[_:=_] M x N) ∷ σ

SubLemma1 : ∀{Γ M σ α τ} → Γ ⊢ M ∷ σ → Γ [ α ≔ᵣ τ ] ⊢ M ∷ (σ [ α ≔ τ ])
SubLemma1 {α = α} (Ax {τ = σ}) with σ
SubLemma1 {α = α} (Ax {τ = σ}) | tvar y with primStringEquality α y
SubLemma1 {α = α} (Ax {τ = σ}) | tvar y | tt = Ax
SubLemma1 {α = α} (Ax {τ = σ}) | tvar y | ff = Ax
SubLemma1 {α = α} (Ax {τ = σ}) | ψ ⇒ φ = Ax
SubLemma1 (Abs p) = Abs (SubLemma1 p)
SubLemma1 (App p q) = App (SubLemma1 p) (SubLemma1 q)

postulate Γ-consistent : ∀ {Γ M σ τ} → (M ∷ σ) ∈ Γ → (M ∷ τ) ∈ Γ → σ is τ ≡ ff → ⊥

{-
SubLemma22 : ∀{Γ M N σ τ x} →
  (var x ∷ τ) :: Γ ⊢ M ∷ σ →
  Γ ⊢ N ∷ τ →
  Γ ⊢ (_[_:=_] M x N) ∷ σ
SubLemma22 .{Γ} .{var x} {N} .{τ} .{τ} .{x} (Ax {Γ} {x} {τ}) b rewrite primStringEqualityRefl {x} = b
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b with inspect (x is y) 
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b | tt with≡ q with inspect (τ is σ)
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b | tt with≡ q | tt with≡ h rewrite q | Strings≡ {x} {y} q | eq=>≡ {τ} {σ} h = Abs (Contract p)
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b | tt with≡ q | ff with≡ h rewrite q | (Strings≡ {x} {y} q) = ⊥-elim (Γ-consistent {(var y ∷ σ) :: (var y ∷ τ) :: Γ} (tl hd) hd h)
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b | ff with≡ q rewrite q with ¬ (x ∈? FV' N) ∨ ¬ (x ∈? FV' M)
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b | ff with≡ q | tt = Abs {!!}
SubLemma22 {Γ} {ƛ (var y) ! M} {N} {σ ⇒ σ'} {τ} {x} (Abs .{(var x ∷ τ) :: Γ} .{var y} .{σ'} .{M} .{σ} p) b | ff with≡ q | ff = {!!}
SubLemma22 {Γ} {ƛ wtf ! M} {N} {σ ⇒ σ'} {τ} {y} (Abs .{(var y ∷ τ) :: Γ} .{wtf} .{σ'} .{M} .{σ} p) b = {!!}
SubLemma22 (App p q) b = App (SubLemma22 p b) (SubLemma22 q b)
-}

reduce : Λ → Λ
reduce ((ƛ x ! M) $ N) = M [ x := N ]
reduce M = M

reduceN : {n : ℕ} → Λ → Λ
reduceN {0} M = M
reduceN{suc n} M = reduceN {n} (reduce M)

--TODO : α-equivalence



data _→β_ : Λ → Λ → Set where
  →β-redex : ∀{x M N} → ((ƛ x ! M) $ N) →β M [ x := N ]
  →β-AR : ∀{F F' x} → F →β F' → ƛ x ! F →β ƛ x ! F'
  →β-RR : ∀{F F' G} → F →β F' → F $ G →β F' $ G
  →β-LR : ∀{F F' G} → F →β F' → G $ F →β G $ F'

data _↠β_ : Λ → Λ → Set where
  to↠β : ∀ {F G} → F →β G → F ↠β G
  ↠β-refl : ∀{F} → F ↠β F
  ↠β-trans : ∀{F G H} → F ↠β G → G ↠β H → F ↠β H

↠β-RR : ∀{F F' G} → F ↠β F' → F $ G ↠β F' $ G
↠β-RR (to↠β x) = to↠β (→β-RR x)
↠β-RR ↠β-refl = ↠β-refl
↠β-RR (↠β-trans p q) = ↠β-trans (↠β-RR p) (↠β-RR q)

↠β-LR : ∀{F F' G} → F ↠β F' → G $ F ↠β G $ F'
↠β-LR (to↠β x) = to↠β (→β-LR x)
↠β-LR ↠β-refl = ↠β-refl
↠β-LR (↠β-trans p q) = ↠β-trans (↠β-LR p) (↠β-LR q)

data _=β_ : Λ → Λ → Set where
  to=β : ∀ {F G} → F →β G → F =β G
  =β-refl : ∀{F} → F =β F
  =β-trans : ∀{F G H} → F =β G → G =β H → F =β H
  =β-sym : ∀{F G} → F =β G → G =β F

=β-redex : ∀{x M N} → ((ƛ x ! M) $ N) =β M [ x := N ]
=β-redex = to=β →β-redex


=β-AR : ∀{F F' x} → F =β F' → ƛ x ! F =β ƛ x ! F'
=β-AR (to=β x) = to=β (→β-AR x)
=β-AR =β-refl = =β-refl
=β-AR (=β-trans p q) = =β-trans (=β-AR p) (=β-AR q)
=β-AR (=β-sym p) = =β-sym (=β-AR p)

=β-RR : ∀{F F' G} → F =β F' → F $ G =β F' $ G
=β-RR (to=β x) = to=β (→β-RR x)
=β-RR =β-refl = =β-refl
=β-RR (=β-trans p q) = =β-trans (=β-RR p) (=β-RR q)
=β-RR (=β-sym p) = =β-sym (=β-RR p)

=β-LR : ∀{F F' G} → F =β F' → G $ F =β G $ F'
=β-LR (to=β x) = to=β (→β-LR x)
=β-LR =β-refl = =β-refl
=β-LR (=β-trans p q) = =β-trans (=β-LR p) (=β-LR q)
=β-LR (=β-sym p) = =β-sym (=β-LR p)

reductionSteps : ℕ → Λ → 𝕃 Λ
reductionSteps (suc n) M = M :: reductionSteps n (reduce M)
reductionSteps 0 M = M :: []

postulate
  SubjectReduction : ∀ {Γ M N σ} → Γ ⊢ M ∷ σ → M →β N → Γ ⊢ N ∷ σ
  SubjectReduction2 : ∀ {Γ M N σ} → Γ ⊢ M ∷ σ → M ↠β N → Γ ⊢ N ∷ σ
  ChurchRosser : ∀{Γ M N N′ σ} → Γ ⊢ M ∷ σ → M ↠β N → M ↠β N′ →
    Σ Λ (λ L → ⟪ ⟪ N ↠β L , N′ ↠β L ⟫ , Γ ⊢ L ∷ σ ⟫)

--(\a.\b.a) c ((\d.e) d)

Ex5 = (ƛ "a" ! ƛ "b" ! var "a") $ var "c" $ ((ƛ "d" ! var "e") $ var "d")


pattern Redex = ((ƛ x ! M) $ N)

{-# TERMINATING #-}
norm : Λ → Maybe Λ
norm Redex = Just  (reduce Redex)
norm (var x) = Just (var x)
norm (M $ N) with norm M | norm N
... | Nothing | Nothing = Nothing
... | Just M' | Nothing = norm (M' $ N)
... | Nothing | Just N' = norm (M $ N')
... | Just M' | Just N' = norm (M' $ N')
norm (ƛ x ! M) with norm M
... | Just M' = norm (ƛ x ! M')
... | Nothing = Nothing


tryNorm : Λ → Λ
tryNorm M with norm M
... | Just M' = M'
... | Nothing = M

postulate
  normIsBeta : ∀{M N} → norm M ≡ Just N → M ↠β N
  typedNotNotImpossible : ∀{Γ M σ} → Γ ⊢ M ∷ σ → norm M ≡ Nothing  → ⊥

normTyped : ∀ {Γ M σ} → Γ ⊢ M ∷ σ → Σ Λ (λ N → norm M ≡ Just N)
normTyped {Γ} {M} {σ} p with inspect (norm M)
... | Just N with≡ q = N , q
... | Nothing with≡ q = ⊥-elim (typedNotNotImpossible p q)


