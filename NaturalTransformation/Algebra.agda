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
    str-∘      : ∀ {A B} {f : A [ C₁ ]⇒ B} {g : F·₁ B ⇒ Ob}
               -> str (g ∘ F⇒₁ f) ≈ str g ∘ F⇒₂ f
    str-resp-≈ : ∀ {A} {f g : F·₁ A ⇒ Ob} -> f ≈ g -> str f ≈ str g

record Relative-N-Algebra {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                          {F₁ F₂ F₃ : Functor C₁ C₂}
                          (N₁ : NaturalTransformation F₁ F₂) (N₂ : NaturalTransformation F₁ F₃)
                          : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₂) where
  open Category C₂; open Functor₁ F₁; open Functor₂ F₂; open Functor₃ F₃
  open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂

  field
    str : ∀ {A B} -> F·₁ A ⇒ F·₃ B -> F·₂ A ⇒ F·₃ B

    ηʳ         : ∀ {A B} {f : F·₁ A ⇒ F·₃ B} -> str f ∘ η₁ ≈ f 
    str-∘₁     : ∀ {A B C} {f : A [ C₁ ]⇒ B} {g : F·₁ B ⇒ F·₃ C}
               -> str (g ∘ F⇒₁ f) ≈ str g ∘ F⇒₂ f
    str-∘₂     : ∀ {A B C} {f : F·₁ A ⇒ F·₃ B} {g : B [ C₁ ]⇒ C} 
               -> str (F⇒₃ g ∘ f) ≈ F⇒₃ g ∘ str f
    str-resp-≈ : ∀ {A B} {f g : F·₁ A ⇒ F·₃ B} -> f ≈ g -> str f ≈ str g
