module Categories.Categories.Nat where

open import Relation.Binary
open import Data.Nat
open import Data.Fin as F

open DecTotalOrder decTotalOrder

open import Categories.Category renaming (zero to lzero)
  
Nat : ℕ -> Category lzero lzero lzero
Nat n = record
  { Obj    = Fin n
  ; _⇒_    = F._≤_
  ; setoid = ⊤-ISetoid
  ; id     = refl
  ; _∘_    = flip trans
  }

Zero = Nat 0
One  = Nat 1
