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

review : ∀ {I i o a} → (l : LensLike Review I i o) → i a → o a
review {a = a} l x = Review.get (LensLike.f l {a} {a} (rev x))

view : ∀ {I i o a} → LensLike (Forget (i a)) I i o → o a → i a
view {i = i} {a = a} (ll l) = Forget.f (l {a} {a} (forget id))

Iso : (I : Set₁) (i o : I → Set) → Set₁
Iso = Family IsProfunctor

iso : ∀ {I i o} → (∀ {a} → o a → i a) → (∀ {a} → i a → o a) → Iso I i o
iso x y {k} {{profunctor}} = ll (dimap x y)
  where open IsProfunctor profunctor

runIso′ : ∀ {I i o} → Iso I i o → ∀ {a b} → Exchange (i a) (i b) (o a) (o b)
runIso′ x = LensLike.f (x {{exchangeProfunctor _ _}}) (exch id id)

runIso : ∀ {I i o} → Iso I i o → (∀ {a} → o a → i a) × (∀ {a} → i a → o a)
runIso {I} x = (λ {a} → Exchange.buy (runIso′ x {a} {a})) ,
                 (λ {a} → Exchange.sell (runIso′ x {a} {a}))

isosym : ∀ {I i o} → Iso I i o → Iso I o i
isosym = uncurry iso ∘ swap ∘ runIso

isoId : ∀ {I i} → Iso I i i
isoId = iso id id
