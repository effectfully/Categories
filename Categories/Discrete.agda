module Categories.Categories.Discrete where

open import Data.Empty
open import Data.Unit.Base
open import Categories.Category

Discrete : ∀ {α} -> Set α -> Category α α _
Discrete A = record
  { Obj    = A
  ; _⇒_    = _≡_
  ; setoid = ⊤-ISetoid
  ; id     = prefl
  ; _∘_    = flip ptrans
  }

Zero = Discrete ⊥
One  = Discrete ⊤
