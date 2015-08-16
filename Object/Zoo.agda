module Categories.Object.Zoo where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

Cone : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> _ -> Functor C₁ C₂ -> Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂)
Cone A₂ F = NaturalTransformation (constᶠ A₂) F
