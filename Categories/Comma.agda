module Categories.Categories.Comma where

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.ZooPlus
open import Categories.Object.Limit.Terminal

module _ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
         {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
         (F₁ : Functor C₁ C₃) (F₂ : Functor C₂ C₃) where
  open import Categories.Morphism.SquareOver F₁ F₂

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

Arrow : ∀ {α β γ} -> Category α β γ -> Category (α ⊔ β) (β ⊔ γ) γ
Arrow C = Comma (idᶠ {C = C}) (idᶠ {C = C})

Slice : ∀ {α β γ} -> (C : Category α β γ) -> _ -> Category (α ⊔ β) (β ⊔ γ) γ
Slice C Z = Comma (idᶠ {C = C}) (constᶠ {C₁ = C} Z)

Cones : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
      -> Functor C₁ C₂ -> Category _ _ _
Cones F = Comma diagonalᶠ (pointᶠ F)

Limit : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
      -> (F : Functor C₁ C₂) -> Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂)
Limit F = Terminal (Cones F)

module Limit {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
             {F : Functor C₁ C₂} = Terminal (Cones F)
