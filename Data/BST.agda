

open import NAL.Data.Bool.Relations using (transitive; total)
open import NAL.Utils.Core renaming (_⊔_ to maxlevel)
open import NAL.Data.Bool
open import NAL.Data.Maybe
open import NAL.Utils.Dependent
open import NAL.Data.List


module NAL.Data.BST {ℓ : Level} {A : Set ℓ} (_≤_ : A → A → 𝔹)
  (≤-trans : transitive _≤_) (≤-total : total _≤_) where

open import NAL.Data.Bool.Relations _≤_

data BST : A → A → Set ℓ where
  Empty : ∀ {l u : A} → l ≤ u ≡ tt → BST l u
  Node : ∀ {l l' u u' : A} →
                (v : A) →
                BST l' v →
                BST v u' →
                l ≤ l' ≡ tt →
                u ≤ u' ≡ tt →
                BST l u
              
search :  ∀ {l u : A} (x : A) → BST l u → Maybe (Σ A (λ (y : A) → (y ⇔ x) ≡ tt))
search x (Empty _) = Nothing
search x (Node v l r _ _) with inspect (x ≤ v) | inspect (v ≤ x)
... | tt with≡ p | tt with≡ q = Just (Σ v , ⇔-intro q p)
... | tt with≡ _ | _ = search x l
... | ff with≡ _ | _ = search x r

preorder-traverse : ∀ {l u : A} → BST l u → 𝕃 A
preorder-traverse (Empty _) = []
preorder-traverse (Node v l r _ _) =
  v :: preorder-traverse l ++ preorder-traverse r
