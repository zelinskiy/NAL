module NAL.Utils.EqReasoning {a} {A : Set a} where
open import NAL.Utils.Core

infix  3 _∎
infixr 2 _≡⟨⟩_ _≡⟨_⟩_ 
infix  1 begin_

begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl
