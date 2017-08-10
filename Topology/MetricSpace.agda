module NAL.Topology.MetricSpace where

open import NAL.Data.Eq
open import NAL.Data.Bool
open import NAL.Data.Either
open import NAL.Data.Float
open import NAL.Utils.Dependent
open import NAL.Utils.Core


private postulate 2-lemma : (a : ℝ) →  a ≥ 0.0 ≡ tt → a + a ≥ 0.0 ≡ tt


record MetricSpace (M : Set) {{eqM : Eq M}} : Set where
  field
    d : M × M → ℝ
    d-id : {x y : M} → d (x , y) ≡ 0.0 iff x ≡ y
    d-sym : {x y : M} → d (x , y) ≡ d (y , x)
    d-tri : {x y z : M} → d (x , y) + d (y , z) ≥ d (x , z) ≡ tt
    d-nneg : (x y : M) → d (x , y) ≥ 0.0 ≡ tt --follows from d-id and d-tri
  {-
  d-nneg : (x y : M) → d (x , y) ≥ 0.0 ≡ tt
  d-nneg x y with inspect (0.0 is d (x , y))
  ... | tt with≡ p rewrite p = b→a∨b {primFloatNumericalLess 0.0 (d (x , y))} refl
  ... | ff with≡ p = a→a∨b {primFloatNumericalLess 0.0 (d (x , y))} {primFloatNumericalEquality 0.0 (d (x , y))} {!!}
  -}

open MetricSpace {{...}} public
