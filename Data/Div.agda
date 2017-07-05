module NAL.Data.Div where

open import NAL.Utils.Size

data ℕₛ : {i : Size} → Set where
    zeroₛ : {i : Size} → ℕₛ {↑ i} 
    sucₛ : {i : Size} → ℕₛ {i} → ℕₛ {↑ i}

pred : {i : Size} → ℕₛ {i} → ℕₛ {i}
pred .{↑ i} (zeroₛ {i}) = zeroₛ {i}
pred .{↑ i} (succ {i} n) = n 

sub : {i : Size} → ℕₛ {i} → ℕₛ {ω} → ℕₛ {i}
sub .{↑ i} (zeroₛ {i}) n = zeroₛ {i}
sub .{↑ i} (succ {i} m) zeroₛ = succ {i} m
sub .{↑ i} (succ {i} m) (succ n) = sub {i} m n


div : {i : Size} → ℕₛ {i} → ℕₛ → ℕₛ {i}
div .{↑ i} (zeroₛ {i}) n = zeroₛ {i}
div .{↑ i} (succ {i} m) n = succ {i} (div {i} (sub {i} m n) n)

data ⊥ : Set where
record ⊤ : Set where
notZero :  ℕₛ → Set
notZero zeroₛ = ⊥
notZero _ = ⊤
