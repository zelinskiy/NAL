module NAL.Examples.Aristotle where

open import NAL.Utils.Core

postulate Term : Set

data Quantity : Set where
  universal particular : Quantity

data Quality : Set where
  affirmative negative : Quality

record CategoricalProposition : Set where
  constructor cp
  field
    quantity : Quantity
    quality : Quality
    subject : Term
    object : Term

postulate holds : CategoricalProposition → Set

-- A
All_are_ : Term → Term → CategoricalProposition
All subject are object = cp universal affirmative subject object

-- I
No_are_ : Term → Term → CategoricalProposition
No subject are object = cp universal negative subject object

-- E
Some_are_ : Term → Term → CategoricalProposition
Some subject are object = cp particular affirmative subject object

-- O
Some_aren't_ : Term → Term → CategoricalProposition
Some subject aren't object = cp particular negative subject object

postulate
  neg : Term → Term
  dneg : ∀ P → neg (neg P) ≡ P

convert : CategoricalProposition → CategoricalProposition
convert (cp quantity quality subject object) =
  cp quantity quality object subject

contrapose : CategoricalProposition → CategoricalProposition
contrapose (cp quantity quality subject object) =
  cp quantity quality (neg subject) (neg object)

complement : Quality → Quality
complement affirmative = negative
complement negative = affirmative

obvert : CategoricalProposition → CategoricalProposition
obvert (cp quantity quality subject object) =
  cp quantity (complement quality) subject (neg object)


postulate
  -- Figure 1
  Barbara : ∀ {S M P} →
    holds (All M are P) →
    holds (All S are M) →
    holds (All S are P)

  Celarent : ∀ {S M P} →
    holds (Some M are P) →
    holds (All S are M) →
    holds (Some S are P)

  Darii : ∀ {S M P} →
    holds (All M are P) →
    holds (No S are M) →
    holds (No S are P)

  Ferio : ∀ {S M P} →
    holds (Some M are P) →
    holds (No S are M) →
    holds (Some S aren't P)

  -- Figure 2

  Cesare : ∀ {S M P} →
    holds (No P are M) →
    holds (All S are M) →
    holds (No S are P)

  Camestres : ∀ {S M P} →
    holds (All P are M) →
    holds (No S are M) →
    holds (No S are P)

  Festino : ∀ {S M P} →
    holds (No P are M) →
    holds (Some S are M) →
    holds (Some S aren't P)

  Baroco : ∀ {S M P} →
    holds (All P are M) →
    holds (Some S aren't M) →
    holds (Some S aren't P)

  -- Figure 3

  Darapti : ∀ {S M P} →
    holds (All M are P) →
    holds (All M are S) →
    holds (Some S are P)

  Disamis : ∀ {S M P} →
    holds (Some M are P) →
    holds (All M are S) →
    holds (Some S are P)

  Datisi : ∀ {S M P} →
    holds (All M are P) →
    holds (Some M are S) →
    holds (Some S are P)

  Felapton : ∀ {S M P} →
    holds (No M are P) →
    holds (All M are S) →
    holds (Some S aren't P)

  Bocardo : ∀ {S M P} →
    holds (Some M aren't P) →
    holds (All M are S) →
    holds (Some S aren't P)

  Ferison : ∀ {S M P} →
    holds (No M are P) →
    holds (Some M are S) →
    holds (Some S aren't P)

  -- Figure 4

  Bramantip : ∀ {S M P} →
    holds (All P are M) →
    holds (All M are S) →
    holds (Some S are P)

  Camenes : ∀ {S M P} →
    holds (All P are M) →
    holds (No M are S) →
    holds (No S are P)

  Dimaris : ∀ {S M P} →
    holds (Some P aren't M) →
    holds (All M are S) →
    holds (Some S aren't P)

  Fesapo : ∀ {S M P} →
    holds (No P are M) →
    holds (All M are S) →
    holds (Some S aren't P)

  Fresison : ∀ {S M P} →
    holds (No P are M) →
    holds (Some M are S) →
    holds (Some S aren't P)
