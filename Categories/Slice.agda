module Categories.Categories.Slice where

open import Categories.Category
open import Categories.Functor

module _ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         (F : Functor C₁ C₂) where
  open import Categories.Morphism.TriangleOver F

  open Functor F; open Category C₁; open Category₂ C₂

  SliceOver : Obj₂ -> Category (α₁ ⊔ β₂) (β₁ ⊔ γ₂) γ₁
  SliceOver Z = record
    { Obj      = ∃ λ A -> F· A ⇒₂ Z
    ; _⇒_      = λ{ (A , f) (B , g) -> f ⇒ₜ g }
    ; setoid   = comapⁱˢ proj₁ setoid
    ; id       = idₜ
    ; _∘_      = _∘ₜ_
    ; idˡ      = idˡ
    ; idʳ      = idʳ
    ; assoc    = assoc
    ; ∘-resp-≈ = ∘-resp-≈
    }

Slice : ∀ {α β γ} -> (C : Category α β γ) -> _ -> Category (α ⊔ β) (β ⊔ γ) γ
Slice C = SliceOver (idᶠ {C = C})
