module Categories.Category.Product where

open import Categories.Utilities.Prelude
open import Categories.Setoid
open import Categories.Category.Core

_×ᶜ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂}
     -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Category (α₁ ⊔ α₂) (β₁ ⊔ β₂) (γ₁ ⊔ γ₂)
C₁ ×ᶜ C₂ = record
  { Obj      = Obj₁ ×ₚ Obj₂
  ; _⇒_      = _⇒₁_ <×> _⇒₂_
  ; setoid   = setoid₁ ×ⁱˢ setoid₂
  ; id       = id₁ , id₂
  ; _∘_      = zip _∘₁_ _∘₂_
  ; idˡ      = idˡ₁ , idˡ₂
  ; idʳ      = idʳ₁ , idʳ₂
  ; assoc    = assoc₁ , assoc₂
  ; ∘-resp-≈ = zip ∘-resp-≈₁ ∘-resp-≈₂
  } where open Category₁ C₁; open Category₂ C₂
