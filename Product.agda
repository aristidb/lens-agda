module Product where

open import Lens
open import Data.Product
open import Function

Swap : Iso (Set × Set) (λ p → proj₁ p × proj₂ p) (λ p → proj₂ p × proj₁ p)
Swap {{pro}} = ll (dimap swap swap)
  where open IsProfunctor pro

open import Data.Nat

review-Swap : _
review-Swap = review Swap (1 , 2)
