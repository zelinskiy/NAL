
module NAL.Examples.EqReasoning-vs-Rewrite where

open import NAL.Data.Nats hiding (+0)

open import NAL.Utils.EqReasoning
open import NAL.Utils.Core


n+0≡n : (n : ℕ) → n + 0 ≡ n
n+0≡n 0 = refl
n+0≡n (suc n) = begin
      (suc n) + 0 ≡⟨ refl ⟩
      suc (n + 0) ≡⟨ cong {f = suc} (n+0≡n n) ⟩
      suc n       ∎

+0 : (n : ℕ) → n + 0 ≡ n
+0 zero = refl
+0 (suc n) rewrite +0 n = refl


------------------------------------------


*-assoc' : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc' zero b c = refl
*-assoc' (suc a) b c =
  begin
    (suc a * b) * c
      ≡⟨ refl ⟩
    (b + a * b) * c
      ≡⟨ *rdistr+ b (a * b) c ⟩
    b * c + (a * b) * c
      ≡⟨ cong {f = (λ x -> b * c + x)} (*-assoc' a b c)  ⟩
    b * c + a * (b * c)
      ≡⟨ refl ⟩
    (suc a) * (b * c)
      ∎ 

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc zero b c = refl
*-assoc (suc a) b c rewrite
  *rdistr+ b (a * b) c |
  *-assoc a b c
  = refl
