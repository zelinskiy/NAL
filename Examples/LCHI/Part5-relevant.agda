module NAL.Examples.LCHI.Part5-relevant where

open import NAL.Data.Bool
open import NAL.Data.String
open import NAL.Data.ListSet
open import NAL.Data.List
open import NAL.Data.Pair
open import NAL.Data.Eq

open import NAL.Utils.Core
open import NAL.Utils.Dependent

open import NAL.Examples.LCHI.Part3 renaming (FV' to λFV; var to lvar; _⊢_∷_ to _⊢ₗ_∷_; Ax to Axₗ; Exchange to Exchangeₗ; Abs to Absₗ; App to Appₗ)
open import NAL.Examples.LCHI.Part5 using (Φ; hvar; _⊃_)

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
