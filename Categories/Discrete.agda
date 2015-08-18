module Categories.Categories.Discrete where

open import Data.Empty

open import Categories.Category renaming (zero to lzero)

Discrete : ∀ {α} -> Set α -> Category α α lzero
Discrete A = record
  { Obj    = A
  ; _⇒_    = _≡_
  ; setoid = ⊤-ISetoid
  ; id     = prefl
  ; _∘_    = flip ptrans
  }

Zero = Discrete ⊥
One  = Discrete ⊤
