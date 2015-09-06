module Categories.NaturalTransformation.Algebra where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

record N-Algebra {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                 {F₁ F₂ : Functor C₁ C₂} (N : NaturalTransformation F₁ F₂)
                 : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₂) where
  open Category C₂
  open Functor₁ F₁; open Functor₂ F₂
  open NaturalTransformation N

  field
    C   : Obj
    str : ∀ {A} -> F·₁ A ⇒ C -> F·₂ A ⇒ C

    ηʳ      : ∀ {A} {f : F·₁ A ⇒ C} -> str f ∘ η ≈ f 
    str-str : ∀ {A B} {f : A [ C₁ ]⇒ B} {g : F·₁ B ⇒ C}
            -> str (str g ∘ η ∘ F⇒₁ f) ≈ str g ∘ F⇒₂ f
