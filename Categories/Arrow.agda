open import Categories.Category

module Categories.Categories.Arrow {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism ℂ
open Category ℂ

Arrow : Category (α ⊔ β) (β ⊔ γ) γ
Arrow = record
  { Obj      = ∃₂ _⇒_
  ; _⇒_      = λ{ (A , B , f) (C , D , g) -> f ⇒ₛ g }
  ; setoid   = comapⁱˢ (λ{ (f₁ , g₂ , _) -> f₁ , g₂ }) (setoid ×ⁱˢ₂ setoid)
  ; id       = idₛ
  ; _∘_      = _∘ₛ_
  ; idˡ      = idˡ , idˡ
  ; idʳ      = idʳ , idʳ
  ; assoc    = assoc , assoc
  ; ∘-resp-≈ = zip ∘-resp-≈ ∘-resp-≈
  }
