open import Categories.Category

module Categories.Object.Colimit.Pushout {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Pushout {A B C : Obj} (f : C ⇒ A) (g : C ⇒ B) : Set (α ⊔ β ⊔ γ) where
  infix 5 _↖_⟨_⟩

  field
    Ob     : Obj
    ι¹     : A ⇒ Ob
    ι²     : B ⇒ Ob
    _↖_⟨_⟩ : ∀ {D} -> (p : A ⇒ D) -> (q : B ⇒ D) -> .(p ∘ f ≈ q ∘ g) -> Ob ⇒ D

    .comm      : ι¹ ∘ f ≈ ι² ∘ g
    .↖-inj     : ∀ {D} {p₁ p₂ : A ⇒ D} {q₁ q₂ : B ⇒ D} {r : p₁ ∘ f ≈ q₁ ∘ g} {s : p₂ ∘ f ≈ q₂ ∘ g}
               -> p₁ ↖ q₁ ⟨ r ⟩ ≈ p₂ ↖ q₂ ⟨ s ⟩ -> p₁ ≈ p₂ ×ₚ q₁ ≈ q₂
    .Object : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {u : Ob ⇒ D}
               -> (r : u ∘ ι¹ ≈ p) -> (s : u ∘ ι² ≈ q) -> p ↖ q ⟨ r ⌈ ∘²-resp-≈ˡ comm ⌉ˡ s ⟩ ≈ u

  .η : ι¹ ↖ ι² ⟨ _ ⟩ ≈ id
  η = Object idˡ idˡ

  .∘-η : ∀ {D} {u : Ob ⇒ D} -> u ∘ ι¹ ↖ u ∘ ι² ⟨ _ ⟩ ≈ u
  ∘-η = Object refl refl

  .↖-ι¹ : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {r : p ∘ f ≈ q ∘ g}
        -> (p ↖ q ⟨ r ⟩) ∘ ι¹ ≈ p
  ↖-ι¹ = proj₁ (↖-inj ∘-η)

  .↖-ι² : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {r : p ∘ f ≈ q ∘ g}
        -> (p ↖ q ⟨ r ⟩) ∘ ι² ≈ q
  ↖-ι² = proj₂ (↖-inj ∘-η)

  .↖-∘ : ∀ {D E} {p : A ⇒ D} {q : B ⇒ D} {r : D ⇒ E} {s : p ∘ f ≈ q ∘ g}
       -> (r ∘ p) ↖ (r ∘ q) ⟨ _ ⟩ ≈ r ∘ (p ↖ q ⟨ s ⟩)
  ↖-∘ = Object (∘ˡ-resp-≈ˡ ↖-ι¹) (∘ˡ-resp-≈ˡ ↖-ι²)

  .↖-resp-≈ : ∀ {D} {p₁ p₂ : A ⇒ D} {q₁ q₂ : B ⇒ D} {r : p₁ ∘ f ≈ q₁ ∘ g}
            -> (s : p₁ ≈ p₂) -> (t : q₁ ≈ q₂) -> p₁ ↖ q₁ ⟨ r ⟩ ≈ p₂ ↖ q₂ ⟨ s ⌈ r ⌉ˡ t ⟩ 
  ↖-resp-≈ p q = Object (left ↖-ι¹ p) (left ↖-ι² q)
