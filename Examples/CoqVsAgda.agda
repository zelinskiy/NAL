module NAL.Examples.CoqVsAgda where

{-
Theorem pr14: forall (P Q: Type -> Prop),
    (exists x: Type, P x -> Q x) ->
    (forall x: Type, P x) -> exists x: Type, Q x.
Proof.
  intros.
  elim H.
  intros.
  exists x.
  apply H1.
  exact (H0 x).
Qed.
-}

Prop = Set
Type = Set

open import NAL.Utils.Dependent
pr14 : ∀ {P Q : Type → Prop} →
  Σ Type (λ x → P x → Q x) →
  ((x : Type) → P x) → 
  Σ Type Q
pr14 S P = Σ (π₁ S) , (π₂ S (P (π₁ S)))
