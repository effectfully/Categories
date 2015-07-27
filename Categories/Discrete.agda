module Categories.Categories.Discrete where

open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base

open import Categories.Category

Discrete : ∀ {α} -> Set α -> Category α α zero
Discrete A = record
  { Obj      = A
  ; _⇒_      = _≡_
  ; setoid   = ⊤-ISetoid
  ; id       = refl
  ; _∘_      = flip trans
  ; idˡ      = _
  ; idʳ      = _
  ; assoc    = _
  ; ∘-resp-≈ = _
  }

One = Discrete ⊤
