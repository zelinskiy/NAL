module NAL.Examples.CoqVsAgda where

{-
Theorem pr14: forall (P Q: Type -> Prop),
    ({x: Type | P x -> Q x}) ->
    (forall x: Type, P x) -> {x: Type | Q x}.
Proof.
  intros.
  elim H.
  intros.
  exists x.
  apply H1.
  exact (H0 x).
Qed.

Without tactics :

Proof (fun _ _ S F => exist _ (proj1_sig S) (proj2_sig S (F (proj1_sig  S)))).

-}


open import NAL.Utils.Dependent
pr14 : ∀ (P Q : Set → Set) →
  Σ Set (λ x → P x → Q x) →
  ((x : Set) → P x) → 
  Σ Set Q
pr14 _ _ S F = (π₁ S) , (π₂ S (F (π₁ S)))
