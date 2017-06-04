module NAL.Lambda.LambdaPi (V : Set) where

open import NAL.Data.List
open import NAL.Data.Either
open import NAL.Utils.Core

{-
SYSTEM λΠ:


--------
[] ∈ WF



  Γ ⊢ T : S
-------------
Γ, x : T ∈ WF



     Γ ∈ WF
---------------
Γ ⊢ Type : Kind



Γ ∈ WF      x : T ∈ Γ
--------------------
     Γ ⊢ x : T



Γ ⊢ A : Type          x : T ∈ Γ
-------------------------------
            Γ ⊢ x : T



Γ ⊢ A : Type         Γ, x : A ⊢ B : S
-------------------------------------
       Γ ⊢ (Π x : A => B) : S



Γ ⊢ Π x : A => B : S         Γ, x : A ⊢ b : B
---------------------------------------------
      Γ ⊢ Λ x : A => b : Π x : A => B



Γ ⊢ t₁ : Π x : A => B         Γ ⊢ t₂ : A
----------------------------------------
     Γ ⊢ (t₁ $ t₂) : B [x := t₂]



Γ ⊢ A : S          Γ ⊢ B : S         Γ ⊢ a : A         A =β= B
--------------------------------------------------------------
                           Γ ⊢ a : B



-}

data T : Set where
  Type : T
  Kind : T
  var : V → T
  _$_ : T → T → T
  Λ_∈_=>_ : V → T → T → T
  Π_∈_=>_ : V → T → T → T

data Binding : Set where
   _∷_ : T → T → Binding
  

Context = 𝕃 Binding

--TODO: make ⊢ (Γ ⊢ x : X)
-- idea : make instances of ∈WF
data _∈WF {A : Set} (a : A) : Set where
  secret : a ∈WF

Γ-intro : [] ∈WF
Γ-intro = secret

var-intro : ∀ {Γ : Context} {x : V} {t : T} →
  Either ((t ∷ Type) ∈ Γ) ((t ∷ Kind) ∈ Γ) →
  ((var x ∷ t) :: Γ) ∈WF
var-intro _ = secret

type-has-kind : ∀ {Γ : Context} {p : Γ ∈WF} → (Type ∷ Kind) ∈ Γ
type-has-kind = {!!}

-- ...
