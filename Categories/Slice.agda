open import Categories.Category

module Categories.Categories.Slice {α β γ} (C : Category α β γ) where

open import Categories.Morphism C 
open Category C

Slice : Obj -> Category (α ⊔ β) (β ⊔ γ) γ
Slice C = record
  { Obj      = ∃ (_⇒ C)
  ; _⇒_      = λ{ (B , g) (A , f) -> g ⇒ₜ f }
  ; setoid   = comapⁱˢ proj₁ setoid
  ; id       = idₜ
  ; _∘_      = _∘ₜ_
  ; idˡ      = idˡ
  ; idʳ      = idʳ
  ; assoc    = assoc
  ; ∘-resp-≈ = ∘-resp-≈
  }
