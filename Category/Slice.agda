open import Categories.Category.Base

module Categories.Category.Slice {α β γ} (C : Category α β γ) where

open import Data.Product

open Category C

slice : Obj -> Category (α ⊔ β) (β ⊔ γ) γ
slice C = record
  { Obj      = ∃ (_⇒ C)
  ; _⇒_      = λ{ (A , f) (B , g) -> ∃ λ h -> g ∘ h ≈ f }
  ; setoid   = record
      { _≈_            = λ{ (h₁ , p₁) (h₂ , p₂) -> h₁ ≈ h₂ }
      ; isIEquivalence = record
          { refl  = refl
          ; sym   = sym
          ; trans = trans
          }
      }
  ; id       = id , idʳ
  ; _∘_      = λ{ (h₂ , p₂) (h₁ , p₁) -> h₂ ∘ h₁ , ∘ˡ-resp-≈ʳ p₂ ⋯ p₁ }
  ; idˡ      = idˡ
  ; idʳ      = idʳ
  ; assoc    = assoc
  ; ∘-resp-≈ = ∘-resp-≈
  }
