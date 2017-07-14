module NAL.Data.Int where

-- Non-axiomatic (builtin) integer

open import NAL.Data.Nats

data ℤ : Set where
  pos    : ℕ → ℤ
  negsuc : ℕ → ℤ

{-# BUILTIN INTEGER ℤ    #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}
