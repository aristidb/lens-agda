module Profunctor where

open import Function
open import Relation.Binary.PropositionalEquality

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
                         {f : b → c} {g : a → b} {h : d → e} {i : c → d} →
                         ∀ x → dimap (f ∘ g) (h ∘ i) x ≡ (dimap g h ∘ dimap f i) x

record Review (a b : Set) : Set where
  constructor rev
  field get : b

reviewProfunctor : IsProfunctor Review
reviewProfunctor = record {
                     dimap = λ _ g → rev ∘ g ∘ Review.get;
                     profunctorIdentity = λ _ → refl;
                     profunctorCompose = λ _ → refl }

record Forget (r a b : Set) : Set where
  constructor forget
  field f : a → r

forgetProfunctor : ∀ r → IsProfunctor (Forget r)
forgetProfunctor r = record {
                       dimap = λ f g p → forget (Forget.f p ∘ f);
                       profunctorIdentity = λ _ → refl;
                       profunctorCompose = λ _ → refl }

fnProfunctor : IsProfunctor (λ a b → a → b)
fnProfunctor = record {
                 dimap = λ f g p → g ∘ p ∘ f;
                 profunctorIdentity = λ _ → refl;
                 profunctorCompose = λ _ → refl }

record Exchange (a b s t : Set) : Set where
  constructor exch
  field buy : s → a
        sell : b → t

exchangeProfunctor : ∀ a b → IsProfunctor (Exchange a b)
exchangeProfunctor a b = record {
                           dimap = dimap;
                           profunctorIdentity = λ { (exch buy sell) → refl };
                           profunctorCompose = λ _ → refl }
  where dimap : ∀ {r s t u} → (r → s) → (t → u) → Exchange a b s t → Exchange a b r u
        dimap f g (exch buy sell) = exch (buy ∘ f) (g ∘ sell)
