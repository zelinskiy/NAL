module NAL.Examples.LCHI.Part1-deBruijn where

--Type-free λ-calculus in de Bruijn notation
--https://www.cs.cornell.edu/courses/cs4110/2012fa/lectures/lecture14.pdf

open import NAL.Utils.Core
open import NAL.Data.List
open import NAL.Data.Bool
open import NAL.Data.Eq
open import NAL.Data.Nats
open import NAL.Data.Maybe
open import NAL.Algebra.Functor

infixl 80 _$_
infixr 50 ƛ_

-- ??? n of reductions
--- normalization (Maybe nf)

--using de Bruijn indices
--(λx.λy.λz.xyz >>> λ2.λ1.λ0.210)
data Term : Set where
  var : ℕ → Term
  _$_ : Term → Term → Term
  ƛ_ : Term → Term --Caution here!

instance
  EqTerm : Eq Term
  EqTerm = record {_is_ = _eq_}
    where
      _eq_ : Term → Term → 𝔹
      var n eq var m = m == n
      M $ N eq P $ Q = M eq P ∧ N eq Q
      ƛ M eq ƛ N = M eq N
      _ eq _ = ff




FV0 : 𝕃 ℕ → ℕ → Term → 𝕃 ℕ
FV0 fv n (var m) with m > n
... | tt = m :: fv
... | ff = fv
FV0 fv n (ƛ P) = FV0 fv (n + 1) P
FV0 fv n (P $ Q) = nub (FV0 fv n P ++ FV0 fv n Q)

--Note : do not use 0 for free variables as it is our starting point
FV : Term → 𝕃 ℕ
FV = FV0 [] 0

t0 = var 1 $ var 3 $ var 3

isClosedTerm : Term → 𝔹
isClosedTerm M = length (FV M) is 0

↑ : ℕ → ℕ → Term → Term
↑ i c (var n) with n < c
... | tt = var n
... | ff = var (n + i)
↑ i c (ƛ M) = ƛ (↑ i (c + 1) M)
↑ i c (M $ N) = (↑ i c M) $ (↑ i c N)

↓ : ℕ → ℕ → Term → Term
↓ i c (var n) with n < c
... | tt = var n
... | ff = var (n ∸ i)
↓ i c (ƛ M) = ƛ (↓ i (suc c) M)
↓ i c (M $ N) = (↓ i c M) $ (↓ i c N)

_[_≔_] : Term → ℕ → Term → Term
var y [ x ≔ N ] with y == x
... | tt = N
... | ff = var y
(P $ Q) [ x ≔ N ] = (P [ x ≔ N ]) $ (Q [ x ≔ N ])
(ƛ M) [ x ≔ N ] = ƛ (M [ x + 1 ≔ ↑ 1 0 N ])

β-reduce : Term → Term
β-reduce (var n) = var n
β-reduce ((ƛ M) $ N) = ↓ 1 0 (M [ 0 ≔ ↑ 1 0 N ])
β-reduce (M $ N) = (β-reduce M) $ (β-reduce N)
β-reduce (ƛ M) = ƛ (β-reduce M)

β-norm : ℕ → Term → Term
β-norm 0 M = M
β-norm (suc n) M = β-norm n (β-reduce M)

β-norm-steps' : 𝕃 Term → ℕ → Term → 𝕃 Term
β-norm-steps' log 0       M = log
β-norm-steps' log (suc n) M = β-norm-steps' (M :: log) n (β-reduce M)

β-norm-steps : ℕ → Term → 𝕃 Term
β-norm-steps = help []
  where
    help : 𝕃 Term → ℕ → Term → 𝕃 Term
    help log 0       M = log
    help log (suc n) M = help (M :: log) n (β-reduce M)

------------------------------------------------------------------------------

-- Church numerals : 
-- 0̅ = λs.λz.z       = ƛ ƛ 0
-- 1̅ = λs.λz.s z     = ƛ ƛ 1 0
-- 2̅ = λs.λz.s (s z) = ƛ ƛ 1 (1 0)

church : ℕ → Term
church x = ƛ ƛ help x
  where
    help : ℕ → Term
    help 0 = var 0
    help (suc n) = var 1 $ help n

fromChurch : Term → Maybe ℕ
fromChurch (ƛ ƛ M) = h M
  where
    h : Term → Maybe ℕ
    h (var 0) = Just 0
    h (var 1 $ M) = fmap suc (h M)
    h _ = Nothing
fromChurch _ = Nothing



sucChurch = ƛ ƛ ƛ var 1 $ (var 2 $ var 1 $ var 0)
+Church = ƛ ƛ ƛ ƛ var 3 $ var 1 $ (var 2 $ var 1 $ var 0)
*Church = ƛ ƛ ƛ ƛ var 3 $ (var 2 $ var 1) $ var 0
^Church = ƛ ƛ ƛ ƛ var 3 $ var 2 $ var 1 $ var 0



λtrue  = ƛ ƛ var 1
λfalse = ƛ ƛ var 0
λif = ƛ ƛ ƛ var 2 $ var 1 $ var 0
λand = ƛ ƛ λif $ var 1 $ var 0 $ λfalse
λor = ƛ ƛ λif $ var 1 $ λtrue $ var 0
λnot = ƛ λif $ var 0 $ λfalse $ λtrue

isZero = ƛ var 0 $ (ƛ λfalse) $ λtrue

λpair = ƛ ƛ ƛ var 0 $ var 2 $ var 1
λfst  = ƛ var 0 $ λtrue
λsnd  = ƛ var 0 $ λfalse

-- Kleene's dentist trick
predChurch = ƛ ƛ ƛ λsnd $ (var 2 $ (ƛ λpair $ (var 2 $ (λfst $ var 0)) $ (λfst $ var 0)) $ (λpair $ var 0 $ var 0))

--λf x. if (isZero x) 1̅ (mul x (f (pred x)))
factChurch' = ƛ ƛ λif $ (isZero $ var 0) $ (church 1) $ (*Church $ var 0 $ (var 1 $ (predChurch $ var 0)))

Y = ƛ (ƛ var 1 $ (var 0 $ var 0)) $ (ƛ var 1 $ (var 0 $ var 0))

-- fact3 == 6 but takes about a minute
factChurch = Y $ factChurch'

I = ƛ var 0
K = ƛ ƛ var 2
S = ƛ ƛ ƛ var 3 $ var 1 $ (var 2 $ var 1)
ω = ƛ var 0 $ var 0
Ω = ω $ ω

------------------------------------------------------------------------------

testChurch1 : Term → ℕ → Maybe ℕ
testChurch1 f x = fromChurch (β-norm (x * 3) (f $ (church x)))

testChurch1N : ℕ → Term → ℕ → Maybe ℕ
testChurch1N n f x = fromChurch (β-norm n (f $ (church x)))

testChurch2 : Term → ℕ → ℕ → Maybe ℕ
testChurch2 f x y = fromChurch (β-norm (x + y + 10) (f $ (church x) $ (church y)))


testPred : ℕ → Maybe ℕ
testPred x = testChurch1N (x * 10) predChurch x

--which number of →β sufficient for normaization?
testAdd : ℕ → ℕ → Maybe ℕ
testAdd = testChurch2 +Church

testMul : ℕ → ℕ → Maybe ℕ
testMul = testChurch2 *Church

testPow : ℕ → ℕ → Maybe ℕ
testPow = testChurch2 ^Church
