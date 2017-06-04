module NAL.Logic.Kripke where

open import NAL.Data.String
open import NAL.Data.List
open import NAL.Data.Pair
open import NAL.Data.Either
open import NAL.Utils.Relation
open import NAL.Utils.Core

-- TODO:
-- Cut
-- Quantors
-- ? is Either provide correct INCLUSIVE or semantics ?

data Formula : Set where
  var : String → Formula
  True : Formula
  _⊃_ : Formula → Formula → Formula
  _&_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula


infixr 30 _⊃_
infixl 60 _&_
infixl 55 _∨_

Context : Set
Context = 𝕃 Formula


data _⊢_ : Context → Formula → Set where
  Assume     : ∀ {Γ f} → f :: Γ ⊢ f
  Weaken     : ∀ {Γ f g} → Γ ⊢ f → g :: Γ ⊢ f
  Swap       : ∀ {Γ f g h} → f :: g :: Γ ⊢ h → g :: f :: Γ ⊢ h
  Contract   : ∀ {Γ f h} → f :: Γ ⊢ h → f :: f :: Γ ⊢ h
--Cut        : ∀ {Γ Δ f g} → Γ ⊢ f → f :: Δ ⊢ g → (Γ ++ Δ) ⊢ g

  ⊃-IntroR   : ∀ {Γ f g} → f :: Γ ⊢ g → Γ ⊢ f ⊃ g
  ⊃-IntroL   : ∀ {Γ f g h} → Γ ⊢ f → g :: Γ ⊢ h → (f ⊃ g) :: f :: Γ ⊢ h
  ⊃-Elim     : ∀ {Γ f g} → Γ ⊢ f ⊃ g → Γ ⊢ f → Γ ⊢ g
  
  True-Intro : ∀ {Γ} → Γ ⊢ True
  
  &-IntroR    : ∀ {Γ f g} → Γ ⊢ f → Γ ⊢ g → Γ ⊢ f & g
  &-IntroL    : ∀ {Γ f g h} → f :: g :: Γ ⊢ h → f & g :: Γ ⊢ h
  &-Elim1    : ∀ {Γ f g} → Γ ⊢ f & g → Γ ⊢ f
  &-Elim2    : ∀ {Γ f g} → Γ ⊢ f & g → Γ ⊢ g

--  ∨-IntroL    : ∀ {Γ f g h} → f :: Γ ⊢ h → g :: Γ ⊢ h → f ∨ g :: Γ ⊢ h
  ∨-IntroR1   : ∀ {Γ f g} → Γ ⊢ f → Γ ⊢ f ∨ g
  ∨-IntroR2   : ∀ {Γ f g} → Γ ⊢ g → Γ ⊢ f ∨ g
  ∨-ElimR      : ∀ {Γ f g h} → Γ ⊢ f ⊃ h → Γ ⊢ g ⊃ h → Γ ⊢ f ∨ g → Γ ⊢ h

record KripkeFrame : Set₁ where
  field
    W : Set
    R : W → W → Set
    V : W → String → Set
    preorderR : preorder R
    monotonicV : ∀ {w1 w2} → R w1 w2 → ∀ {i} → V w1 i → V w2 i
  reflexiveR : reflexive R
  reflexiveR = proj₁ preorderR
  transitiveR : transitive R
  transitiveR = proj₂ preorderR

open KripkeFrame
  
_,_⊨_ : ∀ (k : KripkeFrame) → W k → Formula → Set
k , w  ⊨ var x = V k w x
k , w  ⊨ True  = ⊤
k , w₁ ⊨ f ⊃ g = ∀ {w₂ : W k} → R k w₁ w₂ → k , w₂ ⊨ f → k , w₂ ⊨ g
k , w  ⊨ f & g = ⟪ (k , w ⊨ f) , (k , w ⊨ g) ⟫
k , w  ⊨ f ∨ g = Either (k , w ⊨ f) (k , w ⊨ g)

⊨-mono : ∀ {k : KripkeFrame} {w₁ w₂ : W k} {formula : Formula} →
         R k w₁ w₂ →
         k , w₁ ⊨ formula →
         k , w₂ ⊨ formula
⊨-mono {k} {formula = var x} r p = monotonicV k r p
⊨-mono {k} {formula = True} r p = ⊤-intro
⊨-mono {k} {formula = f ⊃ g} r p r' p' = p (transitiveR k r r') p'
⊨-mono {k} {formula = f & g} r < pf , pg > =
  < ⊨-mono {formula = f} r pf , ⊨-mono {formula = g} r pg >
⊨-mono {k} {formula = f ∨ g} r (Left pf) = Left (⊨-mono {formula = f} r pf)
⊨-mono {k} {formula = f ∨ g} r (Right pg) = Right (⊨-mono {formula = g} r pg)

_,_⊨con_ : ∀ (k : KripkeFrame) → W k → Context → Set
k , w ⊨con [] = ⊤
k , w ⊨con (f :: Γ) = ⟪ (k , w ⊨ f) , (k , w ⊨con Γ) ⟫

⊨con-mono : ∀ {k : KripkeFrame} {Γ : Context} {w₁ w₂ : W k} →
         R k w₁ w₂ →
         k , w₁ ⊨con Γ →
         k , w₂ ⊨con Γ
⊨con-mono {k} {[]} _ _ = ⊤-intro
⊨con-mono {k} {f :: Γ} r < u , v > =
  < ⊨-mono {k} {formula = f} r u , ⊨con-mono {k} {Γ} r v >

_⊩_ : Context → Formula → Set₁
Γ ⊩ f = ∀ {k : KripkeFrame} {w : W k} → k , w ⊨con Γ → k , w ⊨ f

soundness : ∀ {Γ : Context} {f : Formula} → Γ ⊢ f → Γ ⊩ f
soundness Assume g = proj₁ g
soundness (Weaken p) g = soundness p (proj₂ g)
soundness  (Swap p) g =
  soundness p < proj₁ (proj₂ g) , < proj₁ g , proj₂ (proj₂ g) > >
soundness (Contract p) g = soundness p < proj₁ g , proj₂ (proj₂ g) >

soundness (⊃-IntroR p) g r u = soundness p < u , ⊨con-mono r g >
soundness (⊃-IntroL p q) {k} g =
  soundness q < proj₁ g (reflexiveR k) (proj₁ (proj₂ g)) , proj₂ (proj₂ g) >
soundness (⊃-Elim p q) {k} g = (soundness p g) (reflexiveR k) (soundness q g)

soundness True-Intro p = ⊤-intro

soundness (&-IntroR pf pg) pfg = < soundness pf pfg , soundness pg pfg >
soundness (&-IntroL p) pfg =
  soundness p  < proj₁ (proj₁ pfg) , < proj₂ (proj₁ pfg) , proj₂ pfg > >
soundness (&-Elim1 pfg) pf = proj₁ (soundness pfg pf)
soundness (&-Elim2 pfg) pg = proj₂ (soundness pfg pg)

--soundness (∨-IntroL p q) < Left g , gc > = soundness p < g , gc >
--soundness (∨-IntroL p q) < Right g , gc > = soundness q < g , gc >
soundness (∨-IntroR1 p) {k} {w} g = Left (soundness p g)
soundness (∨-IntroR2 p) {k} {w} g = Right (soundness p g)
soundness (∨-ElimR fh gh fg){k} gg with soundness fg gg
... | Left x = (soundness fh gg) (reflexiveR k) x
... | Right x = (soundness gh gg) (reflexiveR k) x


data _≼_ : Context → Context → Set where 
  ≼-refl : ∀ {Γ} → Γ ≼ Γ
  ≼-cons : ∀ {Γ Γ' f} → Γ ≼ Γ' → Γ ≼ (f :: Γ')
    
≼-trans : ∀ {Γ Γ' Γ''} → Γ ≼ Γ' → Γ' ≼ Γ'' → Γ ≼ Γ''
≼-trans u ≼-refl = u
≼-trans u (≼-cons u') = ≼-cons (≼-trans u u') 

Weaken≼ : ∀ {Γ Γ'}{f : Formula} → Γ ≼ Γ' → Γ ⊢ f → Γ' ⊢ f
Weaken≼ ≼-refl p = p
Weaken≼ (≼-cons d) p = Weaken (Weaken≼ d p)

U : KripkeFrame
U = record { W = Context ;
             R = _≼_ ;
             preorderR = < ≼-refl , ≼-trans > ;
             V = λ Γ x → Γ ⊢ var x ;
             monotonicV = λ d p → Weaken≼ d p }

TT : (Γ : Context) → (v : Formula) → Γ ⊢ v ⊃ v
TT Γ v = ⊃-IntroR (Assume)

CompletenessU : ∀{f : Formula}{Γ : W U} → U , Γ ⊨ f → Γ ⊢ f 
SoundnessU : ∀{f : Formula}{Γ : W U} → Γ ⊢ f → U , Γ ⊨ f
CompletenessU {var x} u = u
CompletenessU {True} u = True-Intro
CompletenessU {f & g} u =
  &-IntroR (CompletenessU{f} (proj₁ u)) (CompletenessU{g} (proj₂ u))
CompletenessU {f ⊃ g}{Γ} u = 
  ⊃-IntroR
    (CompletenessU {g} 
      (u (≼-cons ≼-refl) (SoundnessU {f} (Assume {Γ}))))
CompletenessU {f ∨ g} {Γ} (Left p) = ∨-IntroR1 (CompletenessU p)
CompletenessU {f ∨ g} {Γ} (Right p) = ∨-IntroR2 (CompletenessU p)
SoundnessU {var x} p = p
SoundnessU {True} p = ⊤-intro
SoundnessU {f & g} p =
  < SoundnessU {f} (&-Elim1 p) , SoundnessU {g} (&-Elim2 p) >
SoundnessU {f ⊃ g} p r u =
  SoundnessU (⊃-Elim (Weaken≼ r p) (CompletenessU {f} u))
SoundnessU {f ∨ g} {Γ} p = {!!}


ctxt-id : ∀{Γ : Context} → U , Γ ⊨con Γ
ctxt-id{[]} = ⊤-intro
ctxt-id{f :: Γ} =
  < SoundnessU{f} Assume , ⊨con-mono (≼-cons ≼-refl) (ctxt-id {Γ}) >

completeness : ∀{Γ : Context}{f : Formula} → Γ ⊩ f → Γ ⊢ f 
completeness {Γ} p = CompletenessU (p{U}{Γ} (ctxt-id{Γ}))


nbe : ∀ {Γ f} → Γ ⊢ f → Γ ⊢ f
nbe {Γ} p = completeness (soundness p)


module Test0 where
  AndTrans : [] ⊢ var "P" & var "Q" ⊃ var "Q" & var "P"
  AndTrans = ⊃-IntroR (&-IntroL (&-IntroR(Weaken Assume) (Swap (Weaken Assume))))
                 

  {-
                     ------ Assume    
                     P ⊢ P           
  ------ Assume      --------- Weaken
  Q ⊢ Q              Q, P ⊢ P        
  -------- Weaken    --------- Swap   
  P, Q ⊢ Q           P, Q ⊢ P
  ------------------------------ &-IntroR
           P, Q ⊢ Q & P
  ------------------------------ &-IntroL
           P & Q ⊢ Q & P
  ------------------------------ ⊃-IntroR
           ⊢ P & Q ⊃ Q & P
     
  -}

  T1 : var "Q" :: [] ⊢ var "P" ⊃ var "Q"
  T1 = ⊃-IntroR (⊃-Elim (⊃-IntroR (Weaken (Weaken Assume))) Assume)
  T1N = nbe T1

  T2 : [] ⊢ True ⊃ True
  T2 = ⊃-IntroR (Weaken True-Intro)
{-
  T3 : (var "A" ⊃ var "Q") :: (var "A" ⊃ var "Q") :: (var "A" ⊃ var "Q") :: [] ⊢ var "Q"
  T3 = {!!}
-}
open Test0
