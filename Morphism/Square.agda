open import Categories.Category

module Categories.Morphism.Square {α β γ} (C : Category α β γ) where

open import Categories.Functor
open import Categories.Morphism.FunSquare (idᶠ {C = C}) (idᶠ {C = C}) public
