module Categories.NaturalTransformation.FunaturalTransformation where

open import Categories.Category
open import Categories.Functor

record FunaturalTransformation {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                               (F₁ F₂ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open Category₁ C₁; open Category₂ C₂
  open Functor₁ F₁; open Functor₂ F₂ 

  field
    η : ∀ {A B} -> A ⇒₁ B -> F·₁ A ⇒₂ F·₂ B

    naturality : ∀ {A B C} {g : B ⇒₁ C} {f : A ⇒₁ B} -> η g ∘₂ F⇒₁ f ≈₂ F⇒₂ g ∘₂ η f
    η-resp-≈   : ∀ {A B} {g f : A ⇒₁ B} -> f ≈₁ g -> η f ≈₂ η g
