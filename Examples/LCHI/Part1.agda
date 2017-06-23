module NAL.Examples.LCHI.Part1 where

--Type-free λ-calculus

open import NAL.Utils.Core
open import NAL.Data.List
open import NAL.Data.Bool
open import NAL.Data.Eq
open import NAL.Data.ListSet
open import NAL.Data.Nats
open import NAL.Data.String

infixl 80 _$_
infixr 50 λ[_]_


--using de Bruijn indices
--(λx.λy.λz.xyz >>> λ2.λ1.λ0.210)
data Term : Set where
  var : String → Term
  _$_ : Term → Term → Term
  λ[_]_ : String → Term → Term --Caution here!

I = λ[ "x" ] var "x"
K = λ[ "x" ] (λ[ "y" ] var "y")
ω = λ[ "x" ] var "x" $ var "x"
Ω = ω $ ω


FV : Term → ListSet String
FV (var s) = singletonSet s
FV (λ[ s ] P) = FV P ─ (singletonSet s)
FV (P $ Q) = FV P ∪ FV Q

isClosedTerm : Term → 𝔹
isClosedTerm M = card (FV M) is 0


--TODO : Make this reliable
newVar : String → String → 𝕃 String → String
newVar x y vs = primStringAppend x "'" 

infixl 100 _[_:=_]

--This is bad, but i cant find any terminating version without de Bruijn indices
{-# NO_TERMINATION_CHECK #-}
_[_:=_] : Term → String → Term → Term
var x [ y := N ] with x is y
... | tt = N
... | ff = var x
(P $ Q) [ x := N ] = (P [ x := N ] $ Q [ x := N ]) 
(λ[ y ] P)[ x := N ] with x is y
(λ[ y ] P)[ x := N ] | tt = λ[ x ] P
(λ[ y ] P)[ x := N ] | ff with ¬ (x ∈? FV N) ∨  ¬ (x ∈? FV P)
(λ[ y ] P)[ x := N ] | ff | tt = (λ[ y ] P [ x := N ])
(λ[ y ] P)[ x := N ] | ff | ff with x ∈? FV N ∧ y ∈? FV P
(λ[ y ] P)[ x := N ] | ff | ff | tt = λ[ z ] P [ y := var z ] [ x := N ] where z = newVar y x [] --Problematic call here
(λ[ y ] P)[ x := N ] | ff | ff | ff = (λ[ y ] P)


--_=α=_ : 
