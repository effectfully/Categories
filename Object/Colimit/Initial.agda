open import Categories.Category

module Categories.Object.Colimit.Initial {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Initial : Set (α ⊔ β ⊔ γ) where
  field
    Ob        : Obj
    ↜         : ∀ {A} -> Ob ⇒ A
    Object : ∀ {A} {f : Ob ⇒ A} -> f ≈ ↜

  η : ∀ {A} {f g : Ob ⇒ A} -> f ≈ g
  η = left Object Object
