module Categories.NaturalTransformation.NaturalIsomorphism where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation.NaturalTransformation
open import Categories.Morphism

record NaturalIsomorphism {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                          (F₁ F₂ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  field
    ₁⇒₂ : NaturalTransformation F₁ F₂
    ₂⇒₁ : NaturalTransformation F₂ F₁

  open NaturalTransformation₁ ₁⇒₂
  open NaturalTransformation₂ ₂⇒₁
  open Morphism C₂

  field
    η-iso : ∀ A -> Iso (ηₑ₁ A) (ηₑ₂ A)
