module Categories.Category.Product where

open import Categories.Utilities.Prelude
open import Categories.Utilities.Product
open import Categories.Category

_×_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂}
    -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Category (α₁ ⊔ α₂) (β₁ ⊔ β₂) (γ₁ ⊔ γ₂)
C₁ × C₂ = record
  { Obj      = Obj₁ ×ₚ Obj₂
  ; _⇒_      = _⇒₁_ -< _×ₚ_ >- _⇒₂_
  ; setoid   = record
      { _≈_            = _≈₁_ -< _×ₚ_ >- _≈₂_
      ; isIEquivalence = record
          { refl  = refl₁ , refl₂
          ; sym   = map sym₁ sym₂
          ; trans = zip trans₁ trans₂
          }
      }
  ; id       = id₁ , id₂
  ; _∘_      = zip _∘₁_ _∘₂_
  ; idˡ      = idˡ₁ , idˡ₂
  ; idʳ      = idʳ₁ , idʳ₂
  ; assoc    = assoc₁ , assoc₂
  ; ∘-resp-≈ = zip ∘-resp-≈₁ ∘-resp-≈₂
  } where open Category₁ C₁; open Category₂ C₂
