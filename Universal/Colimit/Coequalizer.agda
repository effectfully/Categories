open import Categories.Category

module Categories.Universal.Colimit.Coequalizer {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism.Morphism

open IndexedEqReasoningWith ℂ

record Coequalizer {A B : Obj} (f g : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  infixl 5 _↗

  field
    Ob : Obj
    π  : B ⇒ Ob
    _↗ : ∀ {C} -> B ⇒ C -> Ob ⇒ C
    
    comm      : π ∘ f ≈ π ∘ g
    ↗-inj     : ∀ {C} {p q : B ⇒ C} -> p ↗ ≈ q ↗ -> p ≈ q
    universal : ∀ {C} {p : B ⇒ C} {u : Ob ⇒ C} -> u ∘ π ≈ p -> p ↗ ≈ u

  η : π ↗ ≈ id
  η = universal idˡ

  ∘-η : ∀ {C} {u : Ob ⇒ C} -> (u ∘ π) ↗ ≈ u
  ∘-η = universal refl

  ↗-π : ∀ {C} {p : B ⇒ C} -> (p ↗) ∘ π ≈ p
  ↗-π = ↗-inj ∘-η
    
  ↗-resp-≈ : ∀ {C} {p q : B ⇒ C} -> p ≈ q -> p ↗ ≈ q ↗
  ↗-resp-≈ r = universal (left ↗-π r)

  ∘-↗ : ∀ {C D} {q : C ⇒ D} {p : B ⇒ C} -> (q ∘ p) ↗ ≈ q ∘ (p ↗)
  ∘-↗ = universal (∘ˡ-resp-≈ˡ ↗-π)

  π-epi : Epi ℂ π
  π-epi = record
    { epi = λ {_ p q} r ->
        begin
          p         ←⟨ universal r ⟩
          (q ∘ π) ↗ →⟨ ∘-η         ⟩
          q
        ∎
    }
