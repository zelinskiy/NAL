module NAL.Examples.LCHI.Part5 where

open import NAL.Data.Nats
open import NAL.Data.String
open import NAL.Data.List hiding ([_])
open import NAL.Data.ListSet
open import NAL.Data.Eq
open import NAL.Data.Bool
open import NAL.Data.Maybe
open import NAL.Data.Pair

open import NAL.Utils.Core using (_≡_; refl; inspect; _with≡_) 
open import NAL.Utils.Dependent hiding (Π)

open import NAL.Examples.LCHI.Part3 using (Λ; ƛ_!_; _$_; _↠β_; _=β_; _→β_; ↠β-RR; ↠β-LR; =β-RR; =β-LR; =β-AR; Π; tvar; _⇒_; Binding; _∷_; Context) renaming (var to lvar; _⊢_∷_ to _⊢ₗ_∷_; Ax to Axₗ; Exchange to Exchangeₗ; Abs to Absₗ; App to Appₗ)

infixl 10 _#_
infixr 5 _→ᵣ_
infixr 5 _↠ᵣ_
infixr 5 _=ᵣ_

data Comb : Set where
  var : String → Comb
  K S : Comb
  _#_ : Comb → Comb → Comb



data _→ᵣ_ : Comb → Comb → Set where
  →ᵣ-KR : ∀{F G} → K # F # G →ᵣ F
  →ᵣ-SR : ∀{F G H} → S # F # G # H →ᵣ F # H # (G # H)
  →ᵣ-RR : ∀{F F' G} → F →ᵣ F' → F # G →ᵣ F' # G
  →ᵣ-LR : ∀{F F' G} → F →ᵣ F' → G # F →ᵣ G # F'


data _↠ᵣ_ : Comb → Comb → Set where
  to↠ᵣ : ∀ {F G} → F →ᵣ G → F ↠ᵣ G
  rfl : ∀{F} → F ↠ᵣ F
  trans : ∀{F G H} → F ↠ᵣ G → G ↠ᵣ H → F ↠ᵣ H

RR : ∀{G F F'} → F ↠ᵣ F' → F # G ↠ᵣ F' # G
RR (to↠ᵣ x) = to↠ᵣ (→ᵣ-RR x)
RR rfl = rfl
RR (trans p q) = trans (RR p) (RR q)

LR : ∀{G F F'} → F ↠ᵣ F' → G # F ↠ᵣ G # F'
LR (to↠ᵣ x) = to↠ᵣ (→ᵣ-LR x)
LR rfl = rfl
LR (trans p q) = trans (LR p) (LR q)

SR : ∀{F G H} → S # F # G # H ↠ᵣ F # H # (G # H)
SR = to↠ᵣ →ᵣ-SR

KR : ∀{F G} → K # F # G ↠ᵣ F
KR = to↠ᵣ →ᵣ-KR

data _=ᵣ_ : Comb → Comb → Set where
  →ᵣto=ᵣ : ∀ {F G} → F →ᵣ G → F =ᵣ G
  =ᵣ-refl : ∀{F} → F =ᵣ F
  =ᵣ-trans : ∀{F G H} → F =ᵣ G → G =ᵣ H → F =ᵣ H
  =ᵣ-sym : ∀{F G} → F =ᵣ G → G =ᵣ F

I = S # K # K

IR : ∀ {F} →  I # F ↠ᵣ F
IR = trans (to↠ᵣ →ᵣ-SR) (to↠ᵣ →ᵣ-KR)


Ex2 : S # I # I # (S # I # I) ↠ᵣ S # I # I # (S # I # I)
Ex2 = trans (SR) (trans (RR IR) (LR IR))

W = S # S # (K # I)

WR : ∀{F G} → W # F # G ↠ᵣ F # G # G
WR =
  trans (RR SR)
    (trans (RR (LR KR))
      (trans SR (LR IR)))

B = S # (K # S) # K

BR : ∀{F G H} → B # F # G # H ↠ᵣ F # (G # H)
BR =
  trans (RR (RR SR))
    (trans ((RR (RR (RR KR))))
      (trans SR (RR KR)))

C = S # (B # B # S) # (K # K)

CR : ∀{F G H} → C # F # G # H ↠ᵣ F # H # G
CR {F}{G}{H} =
  trans (RR (RR SR))
    (trans (RR (RR (LR KR)))
      (trans (RR (RR (RR BR)))
        (trans (RR BR)
          (trans SR (LR KR)))))

FV : Comb → ListSet String
FV (var x) = singletonSet x
FV (H # G) = FV H ∪ FV G
FV K = ∅
FV S = ∅

_[_≔_] : Comb → String → Comb → Comb
var y [ x ≔ G ] with x is y
... | tt = G
... | ff = var y
(H # E) [ x ≔ G ] = (H [ x ≔ G ]) # (E [ x ≔ G ])
S [ x ≔ G ] = S
K [ x ≔ G ] = K

postulate
  ChurchRosser : ∀ {F F₁ F₂} → F ↠ᵣ F₁ → F ↠ᵣ F₂ →
    Σ Comb (λ G → ⟪ F₁ ↠ᵣ G , F₂ ↠ᵣ G ⟫)

toΛ : Comb → Λ
toΛ (var x) = lvar x
toΛ K = ƛ "x" ! ƛ "y" ! lvar ("x")
toΛ  S = ƛ "x" ! ƛ "y" ! ƛ "z" ! lvar ("x") $ lvar ("z") $ (lvar ("y") $ lvar ("z"))
toΛ (F # G) = toΛ F $ toΛ G

{-
→ᵣ-then-↠β : ∀{F G} → F →ᵣ G → toΛ F ↠β toΛ G
→ᵣ-then-↠β →ᵣ-KR = Σ 5 , {!!}
→ᵣ-then-↠β →ᵣ-SR = {!!}
→ᵣ-then-↠β (→ᵣ-RR p) = {!!}
→ᵣ-then-↠β (→ᵣ-LR p) = {!!}

↠ᵣ-then-↠β : ∀{F G} → F ↠ᵣ G → toΛ F ↠β toΛ G
↠ᵣ-then-↠β (to↠ᵣ x) = {!!}
↠ᵣ-then-↠β rfl = {!!}
↠ᵣ-then-↠β (trans p q) = {!!}
-}

-- TODO : Fix w respect to FV(F)
λ*_!_ : String → Comb → Comb
λ* x ! var y with x is y
... | tt = I
... | ff = K # var y
λ* x ! (F # G) = S # (λ* x ! F) # (λ* x ! G)
λ* x ! F = K # F

{-
redexReduces : ∀{x F G} → (λ* x ! F) # G ↠ᵣ F [ x ≔ G ]
redexReduces = {!!}
-}

toComb : Λ → Comb
toComb (lvar x) = var x
toComb (M $ N) = toComb M # toComb  N
toComb (ƛ x ! M) = λ* x ! toComb M


{-
open _=β_
open _→β_

lemma1 : ∀{x M} → toΛ (toComb (ƛ x ! M)) =β ƛ x ! toΛ (toComb M)
lemma1 {x} {M = lvar y} with x is y
... | tt =  {!!}
... | ff =  to=β ({!!})
lemma1 {x} {M = M $ N} = {!!}
lemma1 {M = ƛ y ! M} = {!!}


toCombToΛ : ∀{M} → toΛ (toComb M) =β M
toCombToΛ {lvar x} = =β-refl
toCombToΛ {M $ N} = =β-trans (=β-RR toCombToΛ) (=β-LR toCombToΛ)
toCombToΛ {ƛ x ! M} = =β-trans (lemma1{x}{M}) (=β-AR toCombToΛ )
-}


data _⊢ₖ_∷_ : Context → Comb → Π → Set where
  Axₖ : ∀{Γ x τ} → (x ∷ τ) :: Γ ⊢ₖ var x ∷ τ
  KAxₖ : ∀ {Γ σ τ} → Γ ⊢ₖ K ∷ σ ⇒ τ ⇒ σ
  SAxₖ : ∀ {Γ σ τ ρ} → Γ ⊢ₖ S ∷ (σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ
  Appₖ : ∀ {Γ M N σ τ} → Γ ⊢ₖ M ∷ σ ⇒ τ → Γ ⊢ₖ N ∷ σ → Γ ⊢ₖ M # N ∷ τ

Lemma-5-2-3 : ∀ {Γ x F ρ τ} → (x ∷ ρ) :: Γ ⊢ₖ F ∷ τ → Γ ⊢ₖ λ* x ! F ∷ ρ ⇒ τ
Lemma-5-2-3 {x = x}{τ = τ} Axₖ rewrite primStringEqualityRefl {x} = Appₖ (Appₖ SAxₖ KAxₖ) (KAxₖ{τ = τ})
Lemma-5-2-3 KAxₖ = Appₖ KAxₖ KAxₖ
Lemma-5-2-3 SAxₖ = Appₖ KAxₖ SAxₖ
Lemma-5-2-3 (Appₖ p q) = Appₖ (Appₖ SAxₖ (Lemma-5-2-3 p)) (Lemma-5-2-3 q)

Proposition1 : ∀ {Γ F τ} → Γ ⊢ₖ F ∷ τ → Γ ⊢ₗ toΛ F ∷ τ
Proposition1 Axₖ = Axₗ
Proposition1 KAxₖ = Absₗ (Absₗ (Exchangeₗ 0 Axₗ))
Proposition1 SAxₖ = Absₗ (Absₗ (Absₗ (Appₗ (Appₗ (Exchangeₗ 1 (Exchangeₗ 0 Axₗ)) Axₗ) (Appₗ (Exchangeₗ 0 Axₗ) Axₗ))))
Proposition1 (Appₖ p q) = Appₗ (Proposition1 p) (Proposition1 q)

Proposition2 : ∀ {Γ F τ} → Γ ⊢ₗ F ∷ τ → Γ ⊢ₖ toComb F ∷ τ
Proposition2 Axₗ = Axₖ
Proposition2 (Absₗ p) = Lemma-5-2-3 (Proposition2 p)
Proposition2 (Appₗ p q) = Appₖ (Proposition2 p) (Proposition2 q)

infixr 50 _⊃_

data Φ : Set where
  hvar : String → Φ
  _⊃_ : Φ → Φ → Φ
  ⊥ : Φ

_[_] : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → ℕ → Maybe A
[] [ n ] = Nothing
(x :: xs) [ 0 ] = Just x
(x :: xs) [ suc n ] = xs [ n ]

removeAt : ∀ {ℓ} {A : Set ℓ} → ℕ → 𝕃 A → 𝕃 A
removeAt _ [] = []
removeAt 0 (x :: xs) = xs
removeAt (suc n) (x :: xs) = x :: removeAt n xs

data _⊢ₕₚ_ : 𝕃 Φ → 𝕃 Φ → Set where
  H-[] : ∀ {Γ} → Γ ⊢ₕₚ []
  H-As : ∀ {Γ A p} → (i : ℕ) → Γ [ i ] ≡ Just A → Γ ⊢ₕₚ p → removeAt i Γ ⊢ₕₚ (A :: p)
  H-Ex : ∀ {Γ A p} → Γ ⊢ₕₚ p → Γ ⊢ₕₚ ((⊥ ⊃ A) :: p)
  H-AxK : ∀ {Γ A B p} → Γ ⊢ₕₚ p → Γ ⊢ₕₚ ((A ⊃ (B ⊃ A)) :: p)
  H-AxS : ∀ {Γ A B C p} → Γ ⊢ₕₚ p → Γ ⊢ₕₚ (((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))) :: p)
  H-MP : ∀ {Γ A B p} → (i j : ℕ) →
    {f : p [ i ] ≡ Just (A ⊃ B)} → {a : p [ j ] ≡ Just A} → Γ ⊢ₕₚ p → Γ ⊢ₕₚ (B :: p)


_⊢ₕ_ : 𝕃 Φ → Φ → Set
Γ ⊢ₕ φ = Σ (𝕃 Φ) (λ p → Γ ⊢ₕₚ (φ :: p))

{-
H-Id : ∀ {Γ φ} → Γ ⊢ₕ (φ ⊃ φ)
H-Id {φ = φ} =
      {- 1 -} Σ (φ ⊃ (ψ ⊃ φ) ⊃ φ) ⊃ ((φ ⊃ (ψ ⊃ φ)) ⊃ (φ ⊃ φ)) -- Axiom S 
      {- 2 -} :: φ ⊃ (ψ ⊃ φ) ⊃ φ -- Axiom K
      {- 3 -} :: (φ ⊃ (ψ ⊃ φ)) ⊃ (φ ⊃ φ) -- MP 1 2
      {- 4 -} :: φ ⊃ (ψ ⊃ φ) -- Axiom K
      {- 5 -} :: [] -- φ ⊃ φ  MP 3 4
  , {!!}
  where ψ = hvar "ψ" --Arbitrary
-}
