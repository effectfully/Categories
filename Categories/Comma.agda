open import Categories.Category.Category
open import Categories.Functor.Functor

module Categories.Categories.Comma
  {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
  {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
  (F₁ : Functor C₁ C₃) (F₂ : Functor C₂ C₃) where

open import Categories.Morphism.FunSquare F₁ F₂

open Functor₁ F₁; open Functor₂ F₂
open Category₁ C₁; open Category₂ C₂

Comma : Category (α₁ ⊔ α₂ ⊔ β₃) (β₁ ⊔ β₂ ⊔ γ₃) (γ₁ ⊔ γ₂)
Comma = record
  { Obj      = ∃₂ λ A₁ A₂ -> F·₁ A₁ [ C₃ ]⇒ F·₂ A₂
  ; _⇒_      = λ{ (_ , _ , h₁) (_ , _ , h₂) -> h₁ ⇒ₛ h₂ }
  ; setoid   = comapⁱˢ₁ (λ{ (f₁ , f₂ , _) -> f₁ , f₂ }) (setoid₁ ×ⁱˢ setoid₂)
  ; id       = idₛ
  ; _∘_      = _∘ₛ_
  ; idˡ      = idˡ₁ , idˡ₂
  ; idʳ      = idʳ₁ , idʳ₂
  ; assoc    = assoc₁ , assoc₂
  ; ∘-resp-≈ = zip ∘-resp-≈₁ ∘-resp-≈₂
  }
