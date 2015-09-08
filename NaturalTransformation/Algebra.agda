module Categories.NaturalTransformation.Algebra where

-- What are the actual coherence rules?

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

record N-Algebra {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                 {F₁ F₂ : Functor C₁ C₂} (N : NaturalTransformation F₁ F₂)
                 : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₂) where
  open Category C₂; open Functor₁ F₁; open Functor₂ F₂; open NaturalTransformation N

  field
    Ob  : Obj
    str : ∀ {A} -> F·₁ A ⇒ Ob -> F·₂ A ⇒ Ob

    ηʳ         : ∀ {A} {f : F·₁ A ⇒ Ob} -> str f ∘ η ≈ f
    str-∘      : ∀ {A B} {g : F·₁ B ⇒ Ob} {f : A [ C₁ ]⇒ B}
               -> str (g ∘ F⇒₁ f) ≈ str g ∘ F⇒₂ f
    str-resp-≈ : ∀ {A} {f g : F·₁ A ⇒ Ob} -> f ≈ g -> str f ≈ str g

record Relative-N-Algebra {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                          {F₁ F₂ : Functor C₁ C₂} (F₃ : Functor C₁ C₂)
                          (N : NaturalTransformation F₁ F₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₂) where
  open Category C₂; open Functor₁ F₁; open Functor₂ F₂; open Functor₃ F₃
  open NaturalTransformation N

  field
    str : ∀ {A B} -> F·₁ A ⇒ F·₃ B -> F·₂ A ⇒ F·₃ B

    ηʳ         : ∀ {A B} {f : F·₁ A ⇒ F·₃ B} -> str f ∘ η ≈ f
    str-∘₁     : ∀ {A B C} {g : F·₁ B ⇒ F·₃ C} {f : A [ C₁ ]⇒ B}
               -> str (g ∘ F⇒₁ f) ≈ str g ∘ F⇒₂ f
    str-∘₂     : ∀ {A B C} {g : F·₃ B ⇒ F·₃ C} {f : F·₁ A ⇒ F·₃ B}
               -> str (g ∘ f) ≈ g ∘ str f
    str-resp-≈ : ∀ {A B} {f g : F·₁ A ⇒ F·₃ B} -> f ≈ g -> str f ≈ str g
