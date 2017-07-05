module NAL.Data.Bin where

open import NAL.Data.Nats
open import NAL.Data.Bool
open import NAL.Data.Fin hiding (fromℕ)
open import NAL.Data.List

Bit = Fin 2

0b : Bit
0b = zero

1b : Bit
1b = suc zero

Bin⁺ : Set
Bin⁺ = 𝕃 Bit

data Bin : Set where
  0#  : Bin
  _1# : (bs : Bin⁺) → Bin



private

  fromBits : 𝕃 Bit → Bin
  fromBits []                = 0#
  fromBits (b :: bs) with fromBits bs
  fromBits (b :: bs) | bs′ 1# = (b :: bs′) 1#
  fromBits (zero :: bs) | 0# = 0#
  fromBits ((suc zero) :: bs) | 0# = [] 1#
  fromBits ((suc (suc ())) :: bs) | _
  
  pattern 2+_ n = suc (suc n)

  ntoBits′ : ℕ → ℕ → 𝕃 Bit
  ntoBits′     0      _  = []
  ntoBits′     1      0  = 0b :: 1b :: []
  ntoBits′     1      1  = 1b :: []
  ntoBits′ (2+ k)     0  = 0b :: ntoBits′ (suc k) k
  ntoBits′ (2+ k)     1  = 1b :: ntoBits′ (suc k) (suc k)
  ntoBits′ (suc k) (2+ n) = ntoBits′ k n

fromℕ : ℕ → Bin⁺
fromℕ n = reverse (ntoBits′ n n)

to𝔹 : Bin⁺ → 𝕃 𝔹
to𝔹 = map (λ { zero → ff; _ → tt})
