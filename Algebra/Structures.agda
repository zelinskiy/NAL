module NAL.Algebra.Structures where

open import NAL.Data.Either3
open import NAL.Data.Either
open import NAL.Data.Pair
open import NAL.Utils.Function

--Group-like structures
--http://i.imgur.com/TJw6xwj.png

record Magma {ℓ} (M : Set ℓ) : Set ℓ where
  field
    _+_ : M → M → M


record Quasigroup {ℓ} (M : Set ℓ) : Set ℓ where
  field
    _+_ : M → M → M
    latin : LatinSquare _+_
  toMagma : Magma M
  toMagma = record { _+_ = _+_}


record Loop {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    ε : C
    latin : LatinSquare _+_
  toQuasigroup : Quasigroup C
  toQuasigroup = record { _+_ = _+_; latin = latin}


record Semigroup {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    +-assoc : Associative _+_
  toMagma : Magma C
  toMagma = record { _+_ = _+_}

record Monoid {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    ε : C
    +-assoc : Associative _+_
    ε-id : Either3 (LeftIdentity _+_ ε) (RightIdentity _+_ ε) ⟪ LeftIdentity _+_ ε , RightIdentity _+_ ε ⟫
  toSemigroup : Semigroup C
  toSemigroup = record { _+_ = _+_; +-assoc =  +-assoc }

record CommutativeMonoid {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    ε : C
    +-assoc : Associative _+_
    +-comm : Commutative _+_
    ε-id : Either (LeftIdentity _+_ ε) (RightIdentity _+_ ε)
  ε-id₂ : ⟪ LeftIdentity _+_ ε , RightIdentity _+_ ε ⟫
  ε-id₂ with ε-id
  ... | Left lid =  ⟨ lid , comm+lid→rid _+_ ε +-comm lid ⟩
  ... | Right rid = ⟨ comm+rid→lid _+_ ε +-comm rid , rid ⟩
  toMonoid : Monoid C
  toMonoid = record { _+_ = _+_; +-assoc =  +-assoc; ε = ε; ε-id = Right ε-id₂ }


record Group {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    _¹ : C → C
    ε : C
    +-assoc : Associative _+_
    ε-id : Either3 (LeftIdentity _+_ ε) (RightIdentity _+_ ε) ⟪ LeftIdentity _+_ ε , RightIdentity _+_ ε ⟫
    inverse : Either3 (LeftComplement _¹ _+_ ε) (RightComplement _¹ _+_ ε) ⟪ (LeftComplement _¹ _+_ ε) , (RightComplement _¹ _+_ ε) ⟫
  toMonoid : Monoid C
  toMonoid = record { _+_ = _+_; +-assoc =  +-assoc; ε = ε; ε-id = ε-id }

record AbelianGroup {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    _¹ : C → C
    ε : C
    +-assoc : Associative _+_
    +-comm : Commutative _+_
    ε-id : Either (LeftIdentity _+_ ε) (RightIdentity _+_ ε)
    inverse : Either (LeftComplement _¹ _+_ ε) (RightComplement _¹ _+_ ε)
  ε-id₂ : ⟪ LeftIdentity _+_ ε , RightIdentity _+_ ε ⟫
  ε-id₂ with ε-id
  ... | Left lid =  ⟨ lid , comm+lid→rid _+_ ε +-comm lid ⟩
  ... | Right rid = ⟨ comm+rid→lid _+_ ε +-comm rid , rid ⟩
  toGroup : Group C
  toGroup = record {
            _+_ = _+_
          ; +-assoc =  +-assoc
          ; ε = ε
          ; ε-id = Right ε-id₂
          ; _¹ = _¹
          ; inverse = {!!} }


--Ring-like


record Semiring {ℓ} (C : Set ℓ) : Set ℓ where
  field
    _+_ : C → C → C
    0' : C
    +-assoc : Associative _+_
    +-comm : Commutative _+_
    0-id : LeftIdentity _+_ 0'

    _*_ : C → C → C
    1' : C
    *-assoc : Associative _*_
    1-id : ⟪ LeftIdentity _*_ 1' , RightIdentity _*_ 1' ⟫

    *-ldistr-+ : LeftDistributive _*_ _+_
    *-rdistr-+ : RightDistributive _*_ _+_
    
  toCommutativeMonoid+ : CommutativeMonoid C
  toCommutativeMonoid+ = record { _+_ = _+_; +-assoc =  +-assoc; ε = 0'; ε-id = Left 0-id; +-comm = +-comm }
  toMonoid* : Monoid C
  toMonoid* = record { _+_ = _+_; +-assoc =  +-assoc; ε = 0'; ε-id = Left 0-id }
