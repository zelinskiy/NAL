module NAL.Examples.RelationalAlgebra where

open import NAL.Data.String
open import NAL.Data.Bool
open import NAL.Data.Nats
open import NAL.Data.Vector
open import NAL.Data.List
open import NAL.Utils.Dependent

-- TODO:
-- Coddificate 

data TYPE : Set where
  CHAR : TYPE
  NAT : TYPE
  BOOL : TYPE
  VARCHAR : TYPE 


Attribute : Set
Attribute = Σ String (λ _ → TYPE)

Schema : Set
Schema = 𝕃 Attribute

data Row : Schema → Set where
  EmptyRow : Row []
  ConsRow  : ∀ {s name} → {u : TYPE} → TYPE → Row s → Row (( Σ name , u ) :: s)

π : ∀ {s s' : Schema} {n : ℕ} → 𝕃 String → 𝕍 (Row s) n → 𝕍 (Row s') n
π = {!!}

σ : ∀ {s : Schema} {n m : ℕ} → 𝕍 (Row s) n → (φ : Row s → 𝔹) → 𝕍 (Row s) m
σ = {!!}

ρ : ∀ {s s' : Schema} {n : ℕ} → (a : String) → (b : String) → 𝕍 (Row s) n → 𝕍 (Row s') n
ρ = {!!}
