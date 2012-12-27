module Lens where

open import Relation.Binary.PropositionalEquality
open import Function

record LensLike (k : Set → Set → Set) : Set₁ where
  field I : Set
        i o : I → Set
        f : ∀ {a b} → k (i a) (i b) → k (o a) (o b)

Family : (constraint : (Set → Set → Set) → Set₁) → Set₁
Family constraint = ∀ {k} → {{c : constraint k}} → LensLike k

{-
LensLike : (k : Set → Set → Set) (I : Set₁) (i o : I → Set) → Set₁
LensLike k _ i o = ∀ {a b} → k (i a) (i b) → k (o a) (o b)

Family : (constraint : (Set → Set → Set) → Set₁) (I : Set₁) (i o : I → Set) → Set₁
Family constraint I i o = ∀ {k} → {{c : constraint k}} → LensLike k I i o
-}

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

record Review (a b : Set) : Set where
  constructor rev
  field get : b

review : (l : LensLike Review) → ∀ {a} → LensLike.i l a → LensLike.o l a
review l {a} x = Review.get (LensLike.f l {a} {a} (rev x))

{-
review : ∀ {I i o} → LensLike Review I i o → ∀ {a} → i a → o a
review l {a} x = Review.get (l {a} {a} (rev x))
-}

reviewProfunctor : IsProfunctor Review
reviewProfunctor = record {
                     dimap = λ _ g → rev ∘ g ∘ Review.get;
                     profunctorIdentity = λ _ → refl;
                     profunctorCompose = λ f g h i x → refl }

Forget : (r a b : Set) → Set
Forget r a b = a → r

forgetProfunctor : ∀ r → IsProfunctor (Forget r)
forgetProfunctor r = record {
                       dimap = λ f g p → p ∘ f;
                       profunctorIdentity = λ _ → refl;
                       profunctorCompose = λ f g h i x → refl }

{-
view : ∀ {I i o a} → LensLike (Forget (i a)) I i o → o a → i a
view {a = a} l = l {a} {a} id
-}

fnProfunctor : IsProfunctor (λ a b → a → b)
fnProfunctor = record {
                 dimap = λ f g p → g ∘ p ∘ f;
                 profunctorIdentity = λ _ → refl;
                 profunctorCompose = λ f g h i x → refl }

--f : LensLike (λ a b → a → b) → _
--f l = {!LensLike.f l!}

Iso : Set₁
Iso = Family IsProfunctor

