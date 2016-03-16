module Categories.Functor.ZooPlus where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Fun

diagonalᶠ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
          -> Functor C₂ (Fun C₁ C₂)
diagonalᶠ {C₂ = C₂} = record
  { F·       = constᶠ
  ; F⇒       = constⁿ
  ; F-id     = refl
  ; F-∘      = refl
  ; F-resp-≈ = λ p -> p
  } where open Category C₂
