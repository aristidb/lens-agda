module Product where

open import Lens
open import Profunctor

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

Swap : Iso (Set × Set) (λ p → proj₁ p × proj₂ p) (λ p → proj₂ p × proj₁ p)
Swap {{pro}} = ll (dimap swap swap)
  where open IsProfunctor pro

open import Data.Nat

review-Swap : _
review-Swap = review Swap (1 , 2)

view-Swap : ℕ × ℕ
view-Swap = view Swap (1 , 2)
  where h : IsProfunctor (Forget (ℕ × ℕ))
        h = forgetProfunctor _

{-
SwapSwap : view (Swap ∘ˡ isosym Swap) ≡ view isoId
SwapSwap = {!!}
-}
