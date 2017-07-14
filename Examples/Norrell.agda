module NAL.Examples.Norrell where

open import NAL.Data.Nats
open import NAL.Data.List

infixr 30 _⇒_

data Type : Set where
  ⋆ : Type
  _⇒_ : Type → Type → Type

data Equal? : Type → Type → Set where
  yes : ∀ {τ} → Equal? τ τ
  no  : ∀ {τ σ} → Equal? τ σ

_=?=_ : (σ τ : Type) → Equal? σ τ
⋆ =?= ⋆ = yes
⋆ =?= _ = no
_ =?= ⋆ = no
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ ⇒ τ)   =?= (.σ ⇒ .τ)    | yes       | yes       = yes
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂)    | _         | _         = no


infixl 80 _$_
infixr 50 _Λ_

--using de Bruijn indices
--(λx.λy.λz.xyz >>> λ2.λ1.λ0.210)
data UTerm : Set where
  var : ℕ → UTerm
  _$_ : UTerm → UTerm → UTerm
  _Λ_ : Type → UTerm → UTerm

Context = 𝕃 Type

--Church style encoding
data Term (Γ : Context) : Type → Set where
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  _Λ_ : ∀ σ {τ} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)


erase : ∀ {Γ τ} → Term Γ τ → UTerm
erase (var x) = var (index x)
erase (M $ L) = erase M $ erase L
erase (σ Λ M) = σ Λ (erase M)


data Infer (Γ : Context) : UTerm → Set where
  ok : (τ : Type) (M : Term Γ τ) → Infer Γ (erase M)
  bad : {e : UTerm} → Infer Γ e

infer : (Γ : Context) (t : UTerm) → Infer Γ t

infer Γ (var n)               with Γ ! n
infer Γ (var .(length Γ + n)) | outside n  = bad
infer Γ (var .(index x))      | inside σ x = ok σ (var x)

infer Γ (e₁ $ e₂)                   with infer Γ e₁
infer Γ (e₁ $ e₂)                   | bad     = bad
infer Γ (.(erase t₁) $ e₂)          | ok ⋆ t₁ = bad
infer Γ (.(erase t₁) $ e₂)          | ok (σ ⇒ τ) t₁    with infer Γ e₂
infer Γ (.(erase t₁) $ e₂)          | ok (σ ⇒ τ) t₁    | bad = bad
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁    | ok σ' t₂      with σ =?= σ'
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁    | ok .σ t₂      | yes = ok τ (t₁ $ t₂)
infer Γ (.(erase t₁) $ .(erase t₂)) | ok (σ ⇒ τ) t₁    | ok σ' t₂      | no = bad

infer Γ (σ Λ M)          with infer (σ :: Γ) M
infer Γ (σ Λ .(erase U)) | ok τ U = ok (σ ⇒ τ) (σ Λ U)
infer Γ (σ Λ M)          | bad    = bad 


--I ≡ λ0.0
I0 : UTerm
I0 = ⋆ Λ var 0

--K ≡ λ1.λ0.1
K0 : UTerm
K0 = ⋆ Λ ⋆ Λ var 1

--S ≡ λ2.λ1.λ0.20(10)
S0 : UTerm
S0 = (⋆ ⇒ ⋆ ⇒ ⋆) Λ (⋆ ⇒ ⋆) Λ ⋆ Λ var 2 $ var 0 $ (var 1 $ var 0)

--B ≡ λ2.λ1.λ0.2(10)
B0 : UTerm
B0 = (⋆ ⇒ ⋆) Λ (⋆ ⇒ ⋆) Λ ⋆ Λ var 2 $ (var 1 $ var 0)

--C ≡ λ2.λ1.λ0.201
C0 : UTerm
C0 = (⋆ ⇒ ⋆ ⇒ ⋆) Λ ⋆ Λ ⋆ Λ var 2 $ var 0 $ var 1

--W ≡ λx.λy.x y y
W0 : UTerm
W0 = (⋆ ⇒ ⋆ ⇒ ⋆) Λ ⋆ Λ var 1 $ var 0 $ var 0
