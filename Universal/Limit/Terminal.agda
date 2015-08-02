open import Categories.Category

module Categories.Universal.Limit.Terminal {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Terminal (Ob : Obj) : Set (α ⊔ β ⊔ γ) where
  field
    ↝         : ∀ {A} -> A ⇒ Ob
    universal : ∀ {A} {f : A ⇒ Ob} -> f ≈ ↝

  η : ∀ {A} {f g : A ⇒ Ob} -> f ≈ g
  η = left universal universal
