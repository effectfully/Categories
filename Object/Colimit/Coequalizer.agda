open import Categories.Category

module Categories.Object.Colimit.Coequalizer {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism ℂ

open Category ℂ

record Coequalizer {A B : Obj} (f g : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  infix 5 _↗⟨_⟩

  field
    Ob    : Obj
    π     : B ⇒ Ob
    _↗⟨_⟩ : ∀ {C} -> (p : B ⇒ C) -> .(p ∘ f ≈ p ∘ g) -> Ob ⇒ C
    
    .comm      : π ∘ f ≈ π ∘ g
    .↗-inj     : ∀ {C} {p q : B ⇒ C} {r : p ∘ f ≈ p ∘ g} {s : q ∘ f ≈ q ∘ g}
               -> p ↗⟨ r ⟩ ≈ q ↗⟨ s ⟩ -> p ≈ q
    .universal : ∀ {C} {p : B ⇒ C} {u : Ob ⇒ C}
               -> (r : u ∘ π ≈ p) -> p ↗⟨ r ⌈ ∘²-resp-≈ˡ comm ⌉ˡ r ⟩ ≈ u

  .η : π ↗⟨ _ ⟩ ≈ id
  η = universal idˡ

  .∘-η : ∀ {C} {u : Ob ⇒ C} -> (u ∘ π) ↗⟨ _ ⟩ ≈ u
  ∘-η = universal refl

  .↗-π : ∀ {C} {p : B ⇒ C} {r : p ∘ f ≈ p ∘ g} -> (p ↗⟨ r ⟩) ∘ π ≈ p
  ↗-π = ↗-inj ∘-η

  .∘-↗ : ∀ {C D} {q : C ⇒ D} {p : B ⇒ C} {r : p ∘ f ≈ p ∘ g}
       -> (q ∘ p) ↗⟨ _ ⟩ ≈ q ∘ (p ↗⟨ r ⟩)
  ∘-↗ = universal (∘ˡ-resp-≈ˡ ↗-π)

  .↗-resp-≈ : ∀ {C} {p q : B ⇒ C} {r : p ∘ f ≈ p ∘ g}
            -> (s : p ≈ q) -> p ↗⟨ r ⟩ ≈ q ↗⟨ s ⌈ r ⌉ˡ s ⟩
  ↗-resp-≈ r = universal (left ↗-π r)

  .π-epi : Epi π
  π-epi = λ r -> right (universal r) ∘-η
