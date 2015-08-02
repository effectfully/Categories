module Categories.Functor.Variety where

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor.Functor

Faithful : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         -> (F : Functor C₁ C₂) -> Set (α₁ ⊔ β₁ ⊔ γ₁ ⊔ γ₂)
Faithful {C₁ = C₁} {C₂ = C₂} F = ∀ {A B} -> (f g : A ⇒₁ B) -> F⇒ f ≈₂ F⇒ g -> f ≈₁ g
  where open Functor F; open Category₁ C₁; open Category₂ C₂

Full : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> (F : Functor C₁ C₂) -> Set (α₁ ⊔ β₁ ⊔ β₂ ⊔ γ₂)
Full {C₁ = C₁} {C₂ = C₂} F = ∀ {A B} -> (g : F· A ⇒₂ F· B) -> ∃ λ f -> F⇒ f ≈₂ g
  where open Functor F; open Category₁ C₁; open Category₂ C₂

Endofunctor : ∀ {α β γ} -> Category α β γ -> Set (α ⊔ β ⊔ γ)
Endofunctor C = Functor C C

Bifunctor : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
          -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Category α₃ β₃ γ₃ -> Set _
Bifunctor C₁ C₂ C₃ = Functor (C₁ × C₂) C₃
