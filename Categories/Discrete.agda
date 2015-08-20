module Categories.Categories.Discrete where

open import Data.Empty

open import Categories.Category

Discrete : ∀ {α} -> Set α -> Category α α zero
Discrete A = record
  { Obj    = A
  ; _⇒_    = _≡_
  ; setoid = ⊤-ISetoid
  ; id     = prefl
  ; _∘_    = flip ptrans
  }

Zero = Discrete ⊥
One  = Discrete ⊤
