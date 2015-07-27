module Categories.Categories.Cat where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Discrete
open import Categories.Universal.Limit.Terminal

open import Relation.Binary.PropositionalEquality

Cat-Terminal : Terminal Cat One
Cat-Terminal = record
  { ↝         = record
      { F·       = _
      ; F⇒       = λ _ -> refl
      ; F-id     = _
      ; F-∘      = _
      ; F-resp-≈ = _
      }
  ; universal = Hetero.hetero _
  }
