open import Categories.Category

module Categories.Universal.Colimit.Initial {α β γ} (ℂ : Category α β γ) where

open IndexedEqReasoningWith ℂ

record Initial (Ob : Obj) : Set (α ⊔ β ⊔ γ) where
  field
    ↜         : ∀ {A} -> Ob ⇒ A
    universal : ∀ {A} {f : Ob ⇒ A} -> f ≈ ↜

  η : ∀ {A} {f g : Ob ⇒ A} -> f ≈ g
  η {_} {f} {g} =
    begin
      f →⟨ universal ⟩
      ↜ ←⟨ universal ⟩
      g
    ∎
