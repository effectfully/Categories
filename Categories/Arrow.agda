open import Categories.Category

module Categories.Categories.Arrow {α β γ} (C : Category α β γ) where

open import Categories.Morphism C
open Category C

Arrow : Category (α ⊔ β) (β ⊔ γ) γ
Arrow = record
  { Obj      = ∃₂ _⇒_
  ; _⇒_      = λ{ (A , B , f₁) (C , D , g₂) -> f₁ ⇒ₛ g₂ }
  ; setoid   = comapⁱˢ₁ (λ{ (f₂ , g₁ , _) -> f₂ , g₁ }) (setoid ×ⁱˢ setoid)
  ; id       = idₛ
  ; _∘_      = _∘ₛ_
  ; idˡ      = idˡ , idˡ
  ; idʳ      = idʳ , idʳ
  ; assoc    = assoc , assoc
  ; ∘-resp-≈ = zip ∘-resp-≈ ∘-resp-≈
  }
