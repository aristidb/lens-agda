module Lens where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product

open import Profunctor

record LensLike (k : Set → Set → Set) (I : Set₁) (i o : I → Set) : Set₁ where
  constructor ll
  field f : ∀ {a b} → k (i a) (i b) → k (o a) (o b)

_∘ˡ_ : ∀ {k I i o m} → LensLike k I m o → LensLike k I i m → LensLike k I i o
_∘ˡ_ (ll x) (ll y) = ll (x ∘′ y)

Family : (constraint : (Set → Set → Set) → Set₁) (I : Set₁) (i o : I → Set) → Set₁
Family constraint I i o = ∀ {k} → {{c : constraint k}} → LensLike k I i o

{-
LensLike : (k : Set → Set → Set) (I : Set₁) (i o : I → Set) → Set₁
LensLike k _ i o = ∀ {a b} → k (i a) (i b) → k (o a) (o b)

Family : (constraint : (Set → Set → Set) → Set₁) (I : Set₁) (i o : I → Set) → Set₁
Family constraint I i o = ∀ {k} → {{c : constraint k}} → LensLike k I i o
-}

review : ∀ {I i o a} → (l : LensLike Review I i o) → i a → o a
review {a = a} l x = Review.get (LensLike.f l {a} {a} (rev x))

view : ∀ {I i o a} → LensLike (Forget (i a)) I i o → o a → i a
view {a = a} (ll l) = l {a} {a} id

Iso : (I : Set₁) (i o : I → Set) → Set₁
Iso = Family IsProfunctor

iso : ∀ {I i o} → (∀ {a} → o a → i a) → (∀ {a} → i a → o a) → Iso I i o
iso x y {k} {{profunctor}} = ll (dimap x y)
  where open IsProfunctor profunctor

runIso : ∀ {I i o} → Iso I i o → (∀ {a} → o a → i a) × (∀ {a} → i a → o a)
runIso x = {!LensLike.f (x {{fnProfunctor}})!}

isosym : ∀ {I i o} → Iso I i o → Iso I o i
isosym iso {k} {{profunctor}} = ll (λ x → {!LensLike.f (iso {k} {{profunctor}})!})
  where open IsProfunctor profunctor
