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

postulate ⊢_ : CategoricalProposition → Set

infixl 1 ⊢_

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
    ⊢ All M are P →
    ⊢ All S are M →
    ⊢ All S are P

  Celarent : ∀ {S M P} →
    ⊢ Some M are P →
    ⊢ All S are M →
    ⊢ Some S are P

  Darii : ∀ {S M P} →
    ⊢ All M are P →
    ⊢ No S are M →
    ⊢ No S are P

  Ferio : ∀ {S M P} →
    ⊢ Some M are P →
    ⊢ No S are M →
    ⊢ Some S aren't P

  -- Figure 2

  Cesare : ∀ {S M P} →
    ⊢ No P are M →
    ⊢ All S are M →
    ⊢ No S are P

  Camestres : ∀ {S M P} →
    ⊢ All P are M →
    ⊢ No S are M →
    ⊢ No S are P

  Festino : ∀ {S M P} →
    ⊢ No P are M →
    ⊢ Some S are M →
    ⊢ Some S aren't P

  Baroco : ∀ {S M P} →
    ⊢ All P are M →
    ⊢ Some S aren't M →
    ⊢ Some S aren't P

  -- Figure 3

  Darapti : ∀ {S M P} →
    ⊢ All M are P →
    ⊢ All M are S →
    ⊢ Some S are P

  Disamis : ∀ {S M P} →
    ⊢ Some M are P →
    ⊢ All M are S →
    ⊢ Some S are P

  Datisi : ∀ {S M P} →
    ⊢ All M are P →
    ⊢ Some M are S →
    ⊢ Some S are P

  Felapton : ∀ {S M P} →
    ⊢ No M are P →
    ⊢ All M are S →
    ⊢ Some S aren't P

  Bocardo : ∀ {S M P} →
    ⊢ Some M aren't P →
    ⊢ All M are S →
    ⊢ Some S aren't P

  Ferison : ∀ {S M P} →
    ⊢ No M are P →
    ⊢ Some M are S →
    ⊢ Some S aren't P

  -- Figure 4

  Bramantip : ∀ {S M P} →
    ⊢ All P are M →
    ⊢ All M are S →
    ⊢ Some S are P

  Camenes : ∀ {S M P} →
    ⊢ All P are M →
    ⊢ No M are S →
    ⊢ No S are P

  Dimaris : ∀ {S M P} →
    ⊢ Some P aren't M →
    ⊢ All M are S →
    ⊢ Some S aren't P

  Fesapo : ∀ {S M P} →
    ⊢ No P are M →
    ⊢ All M are S →
    ⊢ Some S aren't P

  Fresison : ∀ {S M P} →
    ⊢ No P are M →
    ⊢ Some M are S →
    ⊢ Some S aren't P

postulate
  egoists philosophers cynics : Term

All-cynics-are-philosophers :
  ⊢ All egoists are philosophers →
  ⊢ All cynics are egoists →
  ⊢  All cynics are philosophers
All-cynics-are-philosophers A B = {!!}
