module NAL.Algebra.MonadTrans where

open import NAL.Utils.Core
open import NAL.Utils.Function
open import NAL.Algebra.Monad
open import NAL.Data.Maybe


record MonadTrans {ℓ₁ ℓ₂ ℓ₃} (t : (Set ℓ₁ → Set ℓ₂) → Set ℓ₁ → Set ℓ₃) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    lift : {m : Set ℓ₁ → Set ℓ₂}{A : Set ℓ₁}{{_ : Monad m}} → m A → t m A
--    rightZero : {m : Set ℓ₁ → Set ℓ₂}{A : Set ℓ₁}{{r : Monad m}} → (x : A) → lift (Monad.return r x) ≡ Monad.return r x
--    leftDistrib : {M : Set ℓ₁ → Set ℓ₂}{A : Set ℓ₁}{{_ : Monad M}} → (k : A → M A) → lift (? >>= k) ≡ lift ? >>= (lift ∘ k)

data MaybeT {ℓ₁ ℓ₂}(m : Set ℓ₁ → Set ℓ₂)(A : Set ℓ₁) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  mkMaybeT : m (Maybe A) → MaybeT m A

runMaybeT : ∀{ℓ₁ ℓ₂}{m : Set ℓ₁ → Set ℓ₂}{A : Set ℓ₁}{{_ : Monad m}} → MaybeT m A → m (Maybe A)
runMaybeT (mkMaybeT x) = x

open MaybeMonad public

instance
  MonadTransMaybeT : ∀{a b} → MonadTrans{a}{b}{lsuc (a ⊔ b)} (MaybeT{a}{b})
  MonadTransMaybeT = record {
    lift = λ x → mkMaybeT (liftM Just x)}
