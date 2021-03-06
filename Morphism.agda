open import Categories.Category

module Categories.Morphism {α β γ} (C : Category α β γ) where

open import Categories.Morphism.Core      C public
open import Categories.Morphism.Triangle  C public
open import Categories.Morphism.Square    C public
open import Categories.Morphism.Relations C public
