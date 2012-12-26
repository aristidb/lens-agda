module Lens where

open import Relation.Binary.PropositionalEquality
open import Function

LensLike : (k : Set → Set → Set) (I : Set₁) (i o : I → Set) → Set₁
LensLike k _ i o = ∀ {a b} → k (i a) (i b) → k (o a) (o b)

Family : (constraint : (Set → Set → Set) → Set₁) (I : Set₁) (i o : I → Set) → Set₁
Family constraint I i o = ∀ k → constraint k → LensLike k I i o

record IsProfunctor (p : Set → Set → Set) : Set₁ where
  field
    dimap : {a b c d : Set} → (a → b) → (c → d) → p b c → p a d

  lmap : ∀ {a b c} → (a → b) → p b c → p a c
  lmap f = dimap f id

  rmap : ∀ {a b c} → (b → c) → p a b → p a c
  rmap f = dimap id f

  field
    .profunctorIdentity : {a c : Set} → ∀ x → dimap (id {A = a}) (id {A = c}) x ≡ x

    .profunctorCompose : {a b c d e : Set} →
                         (f : b → c) (g : a → b) (h : d → e) (i : c → d) →
                         ∀ x → dimap (f ∘ g) (h ∘ i) x ≡ (dimap g h ∘ dimap f i) x

Review : (a b : Set) → Set
Review a b = b

review : ∀ {I i o} → LensLike Review I i o → ∀ {a} → i a → o a
review l = λ {a} → l {a} {a}

reviewProfunctor : IsProfunctor Review
reviewProfunctor = record {
                     dimap = λ f g → g;
                     profunctorIdentity = λ _ → refl;
                     profunctorCompose = λ f g h i x → refl }

Forget : (r a b : Set) → Set
Forget r a b = a → r

forgetProfunctor : ∀ r → IsProfunctor (Forget r)
forgetProfunctor r = record {
                       dimap = λ f g p → p ∘ f;
                       profunctorIdentity = λ _ → refl;
                       profunctorCompose = λ f g h i x → refl }

forget : ∀ {I i o a} → LensLike (Forget (i a)) I i o → o a → i a
forget {a = a} l = l {a} {a} id

Iso : (I : Set₁) (i o : I → Set) → Set₁
Iso = Family IsProfunctor
