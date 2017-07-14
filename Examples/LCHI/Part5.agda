module NAL.Examples.LCHI.Part5 where

open import NAL.Data.Nats
open import NAL.Data.String
open import NAL.Data.List hiding ([_])
open import NAL.Data.ListSet
open import NAL.Data.Eq
open import NAL.Data.Bool
open import NAL.Data.Maybe
open import NAL.Data.Pair

open import NAL.Utils.Function
open import NAL.Utils.Core using (⊤; ⊤-intro; _≡_; refl; sym; cong; inspect; _with≡_; ⊥-elim; lzero) renaming (⊥ to Bot; trans to trans≡) 
open import NAL.Utils.Dependent hiding (Π)

open import NAL.Examples.LCHI.Part3 using (ran; Λ; ƛ_!_; _$_; _↠β_; _=β_; _→β_; ↠β-RR; ↠β-LR; =β-redex; =β-RR; =β-LR; =β-AR; Π; tvar; _⇒_; Binding; _∷_; Context; _[_:=_]) renaming (FV' to λFV; var to lvar; _⊢_∷_ to _⊢ₗ_∷_; Ax to Axₗ; Exchange to Exchangeₗ; Abs to Absₗ; App to Appₗ)

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



fvS∅ : ∀ {x} → x ∈? FV S ≡ tt → Bot
fvS∅ ()

λ*_!_ : String → Comb → Comb
λ* x ! F with x ∈? FV F
λ* x ! F | ff = K # F
λ* x ! var x' | tt = I
λ* x ! (F # G) | tt = S # λ* x ! F # λ* x ! G
λ* x ! S | tt = K # S --impossible
λ* x ! K | tt = K # K --impossible

irrelevantSubLemma : ∀ {x F G} → x ∈? FV F ≡ ff → F [ x ≔ G ] ≡ F
irrelevantSubLemma {x} {var y} p with inspect (x is y)
... | tt with≡ q rewrite q = 𝔹-contra (sym p)
... | ff with≡ q rewrite p | q = refl
irrelevantSubLemma {F = K} p = refl
irrelevantSubLemma {F = S} p = refl
irrelevantSubLemma {x} {F₁ # F₂} {G} p
  rewrite
    irrelevantSubLemma{x} {F₁}{G} (∪-projL{A = FV F₁} p) |
    irrelevantSubLemma{x} {F₂}{G} (∪-projR{A = FV F₁} p)
    = refl

redexReduces : ∀{x F G} → (λ* x ! F) # G ↠ᵣ F [ x ≔ G ]
redexReduces {x} {F} {G} with inspect (x ∈? FV F)
redexReduces {x} {var y} | ff with≡ p with x is y
redexReduces {x} {var y} | ff with≡ p | tt rewrite p = 𝔹-contra (sym p)
redexReduces {x} {var y} | ff with≡ p | ff = trans KR rfl
redexReduces {x} {K} | ff with≡ p = trans rfl KR
redexReduces {x} {S} | ff with≡ p = KR
redexReduces {x} {F # H} {G} | ff with≡ p with inspect (x ∈? (FV F ∪ FV H))
redexReduces {x} {F # H} {G} | ff with≡ p | tt with≡ q = 𝔹-contra (trans≡ (sym p) q)
redexReduces {x} {F # H} {G} | ff with≡ p | ff with≡ q
  rewrite p
  | irrelevantSubLemma {F = F} {G} (∪-projL{A = FV F} p)
  |  irrelevantSubLemma {F = H} {G} (∪-projR{A = FV F} p)
  = trans KR rfl
redexReduces {x} {var x'} {G} | tt with≡ p rewrite p with x is x'
redexReduces {x} {var x'} {G} | tt with≡ p | tt = trans IR rfl
redexReduces {x} {var x'} {G} | tt with≡ p | ff = trans IR (𝔹-contra p)
redexReduces {x} {F # H} {G} | tt with≡ p rewrite p with inspect (x ∈? (FV F ∪ FV H))
redexReduces {x} {F # H} {G} | tt with≡ p | tt with≡ q =
  trans SR (trans (RR (redexReduces{x} {F}{G})) (trans (LR (redexReduces{x}{H}{G})) rfl))
redexReduces {x} {F # H} {G} | tt with≡ p | ff with≡ q = 𝔹-contra (trans≡ (sym q) p)
redexReduces {x} {S} {G} | tt with≡ p = KR
redexReduces {x} {K} {G} | tt with≡ p = KR


toComb : Λ → Comb
toComb (lvar x) = var x
toComb (t $ u) = toComb t # toComb u
toComb (ƛ x ! t) = λ* x ! toComb t

open _=β_
open _→β_

postulate α-eq : ∀{M N x P} → M =β N → M [ x := P ] =β N [ x := P ]

postulate lemma1 : ∀{x M} → toΛ (toComb (ƛ x ! M)) =β ƛ x ! toΛ (toComb M)
{-
lemma1 : ∀{x M} → toΛ (toComb (ƛ x ! M)) =β ƛ x ! toΛ (toComb M)
lemma1 {x} {M} with inspect (x ∈? FV (toComb M))
lemma1 {x} {lvar y} | tt with≡ p with primStringEquality x y
lemma1 {x} {lvar y} | tt with≡ p | tt rewrite p = {!!}
lemma1 {x} {lvar y} | tt with≡ p | ff rewrite p = 𝔹-contra p
lemma1 {x} {M $ M₁} | tt with≡ p rewrite p = {!!}
lemma1 {x} {ƛ x₁ ! M} | tt with≡ p rewrite p = {!!}
lemma1 {x} {M} | ff with≡ p rewrite p = {!!}
-}

toCombToΛ : ∀{M} → toΛ (toComb M) =β M
toCombToΛ {lvar x} = =β-refl
toCombToΛ {M $ N} = =β-trans (=β-RR toCombToΛ) (=β-LR toCombToΛ)
toCombToΛ {ƛ x ! M} = =β-trans (lemma1{x}{M}) (=β-AR toCombToΛ )


data _⊢ₖ_∷_ : Context → Comb → Π → Set where
  Axₖ : ∀{Γ x τ} → (x ∷ τ) :: Γ ⊢ₖ var x ∷ τ
  KAxₖ : ∀ {Γ σ τ} → Γ ⊢ₖ K ∷ σ ⇒ τ ⇒ σ
  SAxₖ : ∀ {Γ σ τ ρ} → Γ ⊢ₖ S ∷ (σ ⇒ τ ⇒ ρ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ ρ
  Appₖ : ∀ {Γ M N σ τ} → Γ ⊢ₖ M ∷ σ ⇒ τ → Γ ⊢ₖ N ∷ σ → Γ ⊢ₖ M # N ∷ τ

closedTermTypable : ∀{Γ x M σ τ} →
  x ∈? FV M ≡ ff →
  (x ∷ σ) :: Γ ⊢ₖ M ∷ τ →
  Γ ⊢ₖ M ∷ τ
closedTermTypable {x = x} p Axₖ rewrite primStringEqualityRefl {x} =
  𝔹-contra (sym p)
closedTermTypable p KAxₖ = KAxₖ
closedTermTypable p SAxₖ = SAxₖ
closedTermTypable {M = M # _} p (Appₖ q₁ q₂) =
  Appₖ
    (closedTermTypable (∪-projL{A = FV M} p) q₁)
    (closedTermTypable (∪-projR{A = FV M} p) q₂)


Lemma-5-2-3 : ∀ {Γ x F ρ τ} → (x ∷ ρ) :: Γ ⊢ₖ F ∷ τ → Γ ⊢ₖ λ* x ! F ∷ ρ ⇒ τ
Lemma-5-2-3 {x = x}{τ = τ} Axₖ rewrite primStringEqualityRefl {x} =
  Appₖ (Appₖ SAxₖ KAxₖ) (KAxₖ{τ = τ})
Lemma-5-2-3 KAxₖ = Appₖ KAxₖ KAxₖ
Lemma-5-2-3 SAxₖ = Appₖ KAxₖ SAxₖ
Lemma-5-2-3 {x = x}{M # N} (Appₖ p q) with inspect (x ∈? (FV M ∪ FV N))
... | tt with≡ h rewrite h = Appₖ (Appₖ SAxₖ (Lemma-5-2-3 p)) (Lemma-5-2-3 q)
... | ff with≡ h rewrite h = Appₖ KAxₖ (Appₖ
  (closedTermTypable (∪-projL{A = FV M} h) p)
  (closedTermTypable (∪-projR{A = FV M} h) q))


Proposition1 : ∀ {Γ F τ} → Γ ⊢ₖ F ∷ τ → Γ ⊢ₗ toΛ F ∷ τ
Proposition1 Axₖ = Axₗ
Proposition1 KAxₖ = Absₗ (Absₗ (Exchangeₗ 0 Axₗ))
Proposition1 SAxₖ = Absₗ (Absₗ (Absₗ (Appₗ (Appₗ
  (Exchangeₗ 1 (Exchangeₗ 0 Axₗ)) Axₗ) (Appₗ (Exchangeₗ 0 Axₗ) Axₗ))))
Proposition1 (Appₖ p q) = Appₗ (Proposition1 p) (Proposition1 q)

Proposition2 : ∀ {Γ F τ} → Γ ⊢ₗ F ∷ τ → Γ ⊢ₖ toComb F ∷ τ
Proposition2 Axₗ = Axₖ
Proposition2 (Absₗ p) = Lemma-5-2-3 (Proposition2 p)
Proposition2 (Appₗ p q) = Appₖ (Proposition2 p) (Proposition2 q)



infixr 50 _⊃_

data Φ : Set where
  hvar : String → Φ
  _⊃_ : Φ → Φ → Φ

data _⊢ₕₚ_ (Γ : 𝕃 Φ) :  𝕃 Φ → Set where
  H-[] : Γ ⊢ₕₚ []
  H-As : ∀ {A p} → A ∈ Γ → Γ ⊢ₕₚ p → Γ ⊢ₕₚ (A :: p)
  H-AxK : ∀ {A B p} → Γ ⊢ₕₚ p → Γ ⊢ₕₚ ((A ⊃ (B ⊃ A)) :: p)
  H-AxS : ∀ {A B C p} → Γ ⊢ₕₚ p → Γ ⊢ₕₚ (((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))) :: p)
  H-MP : ∀ {A B p} → (A ⊃ B) ∈ p → A ∈ p → Γ ⊢ₕₚ p → Γ ⊢ₕₚ (B :: p) 


_⊢ₕ_ : 𝕃 Φ → Φ → Set
Γ ⊢ₕ φ = Σ (𝕃 Φ) (λ p → Γ ⊢ₕₚ φ :: p)


H-Id : ∀ {Γ A} → Γ ⊢ₕ (A ⊃ A)
H-Id {A = A} =
      Σ (A ⊃ (A ⊃ A)) ⊃ A ⊃ A
      :: A ⊃ A ⊃ A
      :: (A ⊃ ((A ⊃ A) ⊃ A)) ⊃ ((A ⊃ (A ⊃ A)) ⊃ (A ⊃ A))
      :: A ⊃ (A ⊃ A) ⊃ A
      :: []
  , H-MP hd (tl hd) (H-MP (tl hd) (tl (tl hd)) (H-AxK (H-AxS (H-AxK H-[]))))

postulate
  Herbrand1 : ∀ {Γ A B} → A :: Γ ⊢ₕ B → Γ ⊢ₕ A ⊃ B
  Herbrand2 : ∀ {Γ A B} → A :: Γ ⊢ₕ B → Γ ⊢ₕ A ⊃ B
{-
data _⊢ₕₚ′_ (Γ : 𝕃 Φ) :  𝕃 Φ → Set where
  H-[] : Γ ⊢ₕₚ′ []
  H-As : ∀ {A p} → A ∈ Γ → Γ ⊢ₕₚ′ p → Γ ⊢ₕₚ′ (A :: p)
  H-Ex : ∀ {A p} → Γ ⊢ₕₚ′ p → Γ ⊢ₕₚ′ ((⊥ ⊃ A) :: p)
  H-AxK : ∀ {A B p} → Γ ⊢ₕₚ′ p → Γ ⊢ₕₚ′ ((A ⊃ (B ⊃ A)) :: p)
  H-AxS : ∀ {A B C p} → Γ ⊢ₕₚ′ p → Γ ⊢ₕₚ′ (((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))) :: p)
  H-PL : ∀ {A B p} → Γ ⊢ₕₚ′ p → Γ ⊢ₕₚ′ (((A ⊃ B) ⊃ A) ⊃ A :: p)
  H-MP : ∀ {A B p} → (A ⊃ B) ∈ p → A ∈ p → Γ ⊢ₕₚ′ p → Γ ⊢ₕₚ′ (B :: p) 


_⊢ₕ′_ : 𝕃 Φ → Φ → Set
Γ ⊢ₕ′ φ = Σ (𝕃 Φ) (λ p → Γ ⊢ₕₚ′ φ :: p)
-}
toΦ : Π → Φ
toΦ (tvar x) = hvar x
toΦ (φ ⇒ ψ) = (toΦ φ) ⊃ (toΦ ψ)

fromΦ : Φ → Π
fromΦ (hvar x) = tvar x
fromΦ (φ ⊃ ψ) = (fromΦ φ) ⇒ (fromΦ ψ)

∣_∣ : Context → 𝕃 Φ
∣_∣ = map (λ { (x ∷ τ) → toΦ τ}) 

showΦ : Φ → String
showΦ (hvar x) = x
showΦ (φ ⊃ ψ) = primStringAppend (primStringAppend (showΦ ψ) " -> ") (showΦ ψ)

mkΔ : 𝕃 Φ → 𝕃 Binding
mkΔ [] = []
mkΔ  (φ :: φs) = (y ∷ fromΦ φ) :: mkΔ φs where y = primStringAppend "x_" (showΦ φ)


postulate
  Proposition538₁ : ∀{Γ F φ} → Γ ⊢ₖ F ∷ φ → ∣ Γ ∣ ⊢ₕ toΦ φ
  Proposition538₂ : ∀{Γ φ} → Γ ⊢ₕ φ → Σ Comb (λ F → mkΔ Γ ⊢ₖ F ∷ fromΦ φ) 
 

isλI-term : Λ → Set
isλI-term (lvar x) = ⊤
isλI-term (M $ N) = ⟪ isλI-term M , isλI-term N ⟫
isλI-term (ƛ x ! M) = ⟪ isλI-term M , x ∈? λFV M ≡ tt ⟫

isBCK-term : Λ → Set
isBCK-term (lvar x) = ⊤
isBCK-term (M $ N) = ⟪ ⟪ isBCK-term M , isBCK-term N ⟫ , λFV M ∩ λFV N ≡ ∅ ⟫
isBCK-term (ƛ x ! M) = isBCK-term M

isLinearTerm : Λ → Set
isLinearTerm M = ⟪ isλI-term M , isBCK-term M ⟫


data _⊢ᵣₚ_ (Γ : 𝕃 Φ) :  𝕃 Φ → Set where
  R-[] : Γ ⊢ᵣₚ []
  R-AxS : ∀ {A B C p} → Γ ⊢ᵣₚ p → Γ ⊢ᵣₚ (((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))) :: p)
  R-AxB : ∀ {A B C p} → Γ ⊢ᵣₚ p → Γ ⊢ᵣₚ ((B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C :: p)
  R-AxC : ∀ {A B C p} → Γ ⊢ᵣₚ p → Γ ⊢ᵣₚ ((A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C :: p)
  R-AxI : ∀ {A p} → Γ ⊢ᵣₚ p → Γ ⊢ᵣₚ (A ⊃ A :: p)
  R-MP : ∀ {A B p} → (A ⊃ B) ∈ p → A ∈ p → Γ ⊢ᵣₚ p → Γ ⊢ᵣₚ (B :: p) 


_⊢ᵣ_ : 𝕃 Φ → Φ → Set
Γ ⊢ᵣ φ = Σ (𝕃 Φ) (λ p → Γ ⊢ᵣₚ φ :: p)


data _⊢bckp_ (Γ : 𝕃 Φ) :  𝕃 Φ → Set where
  BCK-[] : Γ ⊢bckp []
  BCK-AxB : ∀ {A B C p} → Γ ⊢bckp p → Γ ⊢bckp ((B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C :: p)
  BCK-AxC : ∀ {A B C p} → Γ ⊢bckp p → Γ ⊢bckp ((A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C :: p)
  BCK-AxK : ∀ {A B p} → Γ ⊢bckp p → Γ ⊢bckp (A ⊃ B ⊃ A :: p)
  BCK-MP : ∀ {A B p} → (A ⊃ B) ∈ p → A ∈ p → Γ ⊢bckp p → Γ ⊢bckp (B :: p) 


_⊢bck_ : 𝕃 Φ → Φ → Set
Γ ⊢bck φ = Σ (𝕃 Φ) (λ p → Γ ⊢bckp φ :: p)

data _⊢bcip_ (Γ : 𝕃 Φ) :  𝕃 Φ → Set where
  BCI-[] : Γ ⊢bcip []
  BCI-AxB : ∀ {A B C p} → Γ ⊢bcip p → Γ ⊢bcip ((B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C :: p)
  BCI-AxC : ∀ {A B C p} → Γ ⊢bcip p → Γ ⊢bcip ((A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C :: p)
  BCI-AxI : ∀ {A p} → Γ ⊢bcip p → Γ ⊢bcip (A ⊃ A :: p)
  BCI-MP : ∀ {A B p} → (A ⊃ B) ∈ p → A ∈ p → Γ ⊢bcip p → Γ ⊢bcip (B :: p) 


_⊢bci_ : 𝕃 Φ → Φ → Set
Γ ⊢bci φ = Σ (𝕃 Φ) (λ p → Γ ⊢bcip φ :: p)

infixl 10 _#'_

data Comb' :  Set where
  var' : String → Comb'
  K' S' B' C' I' : Comb'
  _#'_ : Comb' → Comb' → Comb'


FV' : Comb' → ListSet String
FV' (var' x) = singletonSet x
FV' (H #' G) = FV' H ∪ FV' G
FV' com = ∅

--TODO : BCK are BCK-terms and so on

λᵒ_!_ : String → Comb' → Comb'
λᵒ x ! F with x ∈? FV' F
λᵒ x ! F | ff = K' #' F
λᵒ x ! var' x' | tt = I'
λᵒ x ! (F #' G) | tt with x ∈? FV' F | x ∈? FV' G
λᵒ x ! (F #' G) | tt | tt | tt = S' #' λᵒ x ! F #' λᵒ x ! G
λᵒ x ! (F #' G) | tt | tt | ff = C' #' λᵒ x ! F #' λᵒ x ! G
λᵒ x ! (F #' G) | tt | ff | tt = B' #' λᵒ x ! G
λᵒ x ! (F #' G) | tt | ff | ff = K' #' (F #' G)
λᵒ x ! S' | tt = K' #' S' --impossible
λᵒ x ! K' | tt = K' #' K' --impossible
λᵒ x ! B' | tt = K' #' B' --impossible
λᵒ x ! C' | tt = K' #' C' --impossible
λᵒ x ! I' | tt = K' #' I' --impossible

toComb' : Λ → Comb'
toComb' (lvar x) = var' x
toComb' (M $ N) = toComb' M #' toComb' N
toComb' (ƛ x ! M) = λᵒ x ! toComb' M

instance
  EqComb' : Eq Comb'
  EqComb' = record { _is_ = h }
    where
      h : Comb' → Comb' → 𝔹
      h (var' x) (var' y) = x is y
      h (A #' B) (C #' D) = h A C ∧ h B D
      h S' S' = tt
      h K' K' = tt
      h B' B' = tt
      h C' C' = tt
      h I' I' = tt
      h _ _ = ff

getUsedTerms : Comb' → ListSet Comb'
getUsedTerms (var' x) = ∅
getUsedTerms K' = singletonSet K'
getUsedTerms S' = singletonSet S'
getUsedTerms B' = singletonSet B'
getUsedTerms C' = singletonSet C'
getUsedTerms I' = singletonSet I'
getUsedTerms (F #' G) = getUsedTerms F ∪ getUsedTerms G


postulate
  relevantTermsBuiltOfTheorem : ∀{M} → isλI-term M →
    getUsedTerms (toComb' M) is mkLS (S' :: B' :: C' :: I' :: []) ≡ tt
  BCKTermsBuiltOfTheorem : ∀{M} → isBCK-term M →
    getUsedTerms (toComb' M) is mkLS (B' :: C' :: K' :: []) ≡ tt
  linearTermsBuiltOfTheorem : ∀{M} → isLinearTerm M →
    getUsedTerms (toComb' M) is mkLS (B' :: C' :: I' :: []) ≡ tt

--TODO : Proved Relevant Logic Proposition ≅ Typed Relevant Term and so on
