module Categories.Categories.Cat where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.One
open import Categories.Universal.Limit.Terminal

Cat-Terminal : Terminal Cat One
Cat-Terminal = record
  { ↝         = record
      { F·       = λ _ -> _
      ; F⇒       = λ _ -> _
      ; F-id     = _
      ; F-∘      = λ _ _ -> _
      ; F-resp-≈ = λ _ -> _
      }
  ; universal = Hetero.hetero _
  }
