module Product where

open import Lens
open import Data.Product

Swap : Iso (Set × Set) (λ p → proj₁ p × proj₂ p) (λ p → proj₂ p × proj₁ p)
Swap {{pro}} = dimap swap swap
  where open IsProfunctor pro

open import Data.Nat

review-Swap : _
review-Swap = review {Set × Set} {λ p → proj₁ p × proj₂ p}
                {λ p → proj₂ p × proj₁ p} Swap (1 , 2)
