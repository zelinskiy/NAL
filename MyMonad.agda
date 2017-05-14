module MyMonad where
open import Agda.Primitive
open import MyList
open import Utils


record Monad {ℓ₁ ℓ₂} (M : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  field
    return : ∀ {A} → A → M A
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    lidentity : ∀ {A B} → (a : A) (f : A → M B) → (return a) >>= f ≡ f a
    ridentity : ∀ {A} → (m : M A) → m >>= return ≡ m
    --assoc : ∀ {A B C} → (m : M A) (f : A → M B) (g : B → M C) → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)

  
  _>>_ : ∀ {A B} → M A → M B → M B
  M₁ >> M₂ = M₁ >>= λ _ → M₂

  --something must be wrong with ℓ
  _>=>_ : ∀ {A B C : Set ℓ₁}  → (A → M B) → (B → M C) → (A → M C)
  f >=> g = \x -> f x >>= g

open Monad {{...}} public


module Private where
  listBind : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → 𝕃 A → (A → 𝕃 B) → 𝕃 B
  listBind xs f = concat (map f xs)

  concat-single-lemma : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) → concat (xs :: []) ≡ xs
  concat-single-lemma [] = refl
  concat-single-lemma (x :: xs) rewrite concat-single-lemma xs = refl
  
  leftid : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (a : A) (f : A → 𝕃 B) → listBind (singleton a) f ≡ f a
  leftid a f rewrite concat-single-lemma (f a) = refl

  rightid : ∀ {ℓ} {A : Set ℓ} → (xs : 𝕃 A) →
    listBind xs singleton ≡ xs
  rightid [] = refl
  rightid (x :: xs) rewrite rightid xs = refl
  {-
  -- (m >>= f) >>= g
  -- m >>= (\x -> f x >>= g)
  --TODO : Kleisli arrows instead!

  bind-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
           (xs : 𝕃 A) (f : A → 𝕃 B) (g : B → 𝕃 C) →
    concat (map g (concat (map f xs))) ≡
    concat (map (λ x → concat (map g (f x))) xs)
  bind-assoc [] f g = refl
  bind-assoc (x :: xs) f g  = {!refl!}
  -}

  

open Private
instance
  monadList : ∀ {ℓ} →  Monad (𝕃 {ℓ})
  monadList = record {
      return = singleton;
      _>>=_ = listBind;
      lidentity = leftid;
      ridentity = rightid}

