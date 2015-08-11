module Categories.Morphism where

open import Categories.Category

module Morphism {α β γ} (C : Category α β γ) where
  open import Categories.Morphism.Morphism C public
