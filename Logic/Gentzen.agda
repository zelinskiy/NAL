module NAL.Logic.Gentzen (V : Set) where

--Deep magic

-- based on:
-- http://oxij.org/note/ReinventingFormalLogic/
-- disi.unitn.it/~bernardi/RSISE11/Papers/curry-howard.pdf

open import NAL.Data.List
open import NAL.Utils.Dependent

infixr 60 _⊃_

data IPC⟨→⟩ : Set where
  var_  : V → IPC⟨→⟩
  _⊃_ : IPC⟨→⟩ → IPC⟨→⟩ → IPC⟨→⟩
  ⊥  : IPC⟨→⟩


-- Hilbert style sequence

data _hl⊢_ (Γ : 𝕃 IPC⟨→⟩) : 𝕃 IPC⟨→⟩ → Set where


  H-EM : ------------------------------ ([])
                     Γ hl⊢ []


  H-AΓ : ∀ {A pl} →           A ∈ Γ → Γ hl⊢ pl →
                                       ----------------------------- (assumption)
                                            Γ hl⊢ (A :: pl)


  H-AB : ∀ {A pl} →           Γ hl⊢ pl →
                                    -------------------------- (ex falso)
                                    Γ hl⊢ ((⊥ ⊃ A) :: pl)


  H-AK : ∀ {A B pl} →                  Γ hl⊢ pl →
                                      -------------------------------------- (K)
                                      Γ hl⊢ ((A ⊃ (B ⊃ A)) :: pl)


  H-AS : ∀ {A B C pl} →               Γ hl⊢ pl →
                           ---------------------------------------------------------------- (S)
                           Γ hl⊢ (((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C))) :: pl)


  H-IM : ∀ {A B pl} →      (A ⊃ B) ∈ pl → A ∈ pl → Γ hl⊢ pl →
                                     ---------------------------------------------- (MP)
                                                   Γ hl⊢ (B :: pl)


_h⊢_ : (Γ : 𝕃 IPC⟨→⟩) → IPC⟨→⟩ → Set
Γ h⊢ A = Σ (𝕃 IPC⟨→⟩) (λ pl → Γ hl⊢ (A :: pl))


H-AI : ∀ {Γ A} → Γ h⊢ (A ⊃ A)
H-AI {A = A} =
  Σ (A ⊃ A ⊃ A) ⊃ A ⊃ A
  :: A ⊃ A ⊃ A
  :: (A ⊃ (A ⊃ A) ⊃ A) ⊃ (A ⊃ A ⊃ A) ⊃ A ⊃ A
  :: A ⊃ (A ⊃ A) ⊃ A
  :: []
  , H-IM hd (tl hd) (H-IM (tl hd) (tl (tl hd)) (H-AK (H-AS (H-AK H-EM))))


-- Hilbert style tree

data _t⊢_ (Γ : 𝕃 IPC⟨→⟩) : IPC⟨→⟩ → Set where
  T-AΓ : ∀ {A} → A ∈ Γ  → Γ t⊢ A
  T-AB : ∀ {A} → Γ t⊢ (⊥ ⊃ A)
  T-AK : ∀ {A B} → Γ t⊢ (A ⊃ (B ⊃ A))
  T-AS : ∀ {A B C} → Γ t⊢ ((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ B) ⊃ (A ⊃ C)))
  T-IM : ∀ {A B} → Γ t⊢ (A ⊃ B) → Γ t⊢ A → Γ t⊢ B

T-AI : ∀ {Γ A} → Γ t⊢ (A ⊃ A)
T-AI {A = A} = T-IM (T-IM (T-AS {A = A} {B = A ⊃ A} {C = A}) T-AK) T-AK

connect-var : ∀ {Γ L A} → Γ hl⊢ L → A ∈ L → Γ t⊢ A
connect-var H-EM ()
connect-var (H-AΓ y y') hd = T-AΓ y
connect-var (H-AB y) hd = T-AB
connect-var (H-AK y) hd = T-AK
connect-var (H-AS y) hd = T-AS
connect-var (H-IM y y' y0) hd = T-IM (connect-var y0 y) (connect-var y0 y')
connect-var (H-AΓ y y') (tl y0) = connect-var y' y0
connect-var (H-AB y) (tl y') = connect-var y y'
connect-var (H-AK y) (tl y') = connect-var y y'
connect-var (H-AS y) (tl y') = connect-var y y'
connect-var (H-IM y y' y0) (tl y1) = connect-var y0 y1

h→t : ∀ {Γ A} → Γ h⊢ A → Γ t⊢ A
h→t (Σ pl , p) = connect-var p hd

++-proofs : ∀ {Γ L M} → Γ hl⊢ L → Γ hl⊢ M → Γ hl⊢ (L ++ M)
++-proofs H-EM p2 = p2
++-proofs (H-AΓ y y') p2 = H-AΓ y (++-proofs y' p2)
++-proofs (H-AB y) p2 = H-AB (++-proofs y p2)
++-proofs (H-AK y) p2 = H-AK (++-proofs y p2)
++-proofs (H-AS y) p2 = H-AS (++-proofs y p2)
++-proofs (H-IM y y' y0) p2 = H-IM (∈-relax-right y) (∈-relax-right y') (++-proofs y0 p2)

t→h : ∀ {Γ A} → Γ t⊢ A → Γ h⊢ A
t→h (T-AΓ y) = Σ [] , H-AΓ y H-EM
t→h T-AB = Σ [] , H-AB H-EM
t→h T-AK = Σ [] , H-AK H-EM
t→h T-AS = Σ [] , H-AS H-EM
t→h (T-IM {A = A} {B = B} y y') =
  Σ (((A ⊃ B) :: π₁ hA⊃B) ++ (A :: π₁ hA))
  , H-IM hd (∈-relax-left ((A ⊃ B) :: π₁ hA⊃B) hd)
                (++-proofs (π₂ hA⊃B) (π₂ hA))
    where
      hA⊃B = t→h y
      hA = t→h y'


deduction-t : ∀ {Γ A B} → (A :: Γ) t⊢ B → Γ t⊢ (A ⊃ B)
deduction-t (T-AΓ hd) = T-AI
deduction-t (T-AΓ (tl y)) = T-IM T-AK (T-AΓ y)
deduction-t T-AB = T-IM T-AK T-AB
deduction-t T-AK = T-IM T-AK T-AK
deduction-t T-AS = T-IM T-AK T-AS
deduction-t (T-IM y y') = T-IM (T-IM T-AS (deduction-t y)) (deduction-t y')

deduction-h : ∀ {Γ A B} → (A :: Γ) h⊢ B → Γ h⊢ (A ⊃ B)
deduction-h p = t→h (deduction-t (h→t p))



--Gentzen style

data _⊩_ (Γ : 𝕃 IPC⟨→⟩) : IPC⟨→⟩ → Set where
      G-A : ∀ {A} → A ∈ Γ → Γ ⊩ A
      G-B : ∀ {A} → Γ ⊩ ⊥ → Γ ⊩ A 
      G-I : ∀ {A B} → (A :: Γ) ⊩ B → Γ ⊩ (A ⊃ B)
      G-E : ∀ {A B} → Γ ⊩ (A ⊃ B) → Γ ⊩ A → Γ ⊩ B


t→g : ∀ {Γ A} → Γ t⊢ A → Γ ⊩ A
t→g (T-AΓ y) = G-A y
t→g T-AB = G-I (G-B (G-A hd))
t→g T-AK = G-I (G-I (G-A (tl hd))) -- K
t→g T-AS = G-I (G-I (G-I
    (G-E
        (G-E (G-A (tl (tl hd))) (G-A hd))
        (G-E (G-A (tl hd)) (G-A hd))))) -- S
t→g (T-IM y y') = G-E (t→g y) (t→g y')


g→t : ∀ {Γ A} → Γ ⊩ A → Γ t⊢ A
g→t (G-A y) = T-AΓ y
g→t (G-B y) = T-IM T-AB (g→t y)
g→t (G-I y) = deduction-t (g→t y)
g→t (G-E y y') = T-IM (g→t y) (g→t y')

h→g : ∀ {Γ A} → Γ h⊢ A → Γ ⊩ A
h→g p = t→g (h→t p)

g→h : ∀ {Γ A} → Γ ⊩ A → Γ h⊢ A
g→h p = t→h (g→t p)
