open import Categories.Category

module Categories.Object.Limit.Equalizer {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism ℂ

open IEqReasoningWith ℂ

record Equalizer {A B} (f g : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field
    Ob     : Obj
    ι      : Ob ⇒ A
    ⟨_⟩∣_∣ : ∀ {C} -> (p : C ⇒ A) -> .(f ∘ p ≈ g ∘ p) -> C ⇒ Ob

    .comm      : f ∘ ι ≈ g ∘ ι
    .⟨⟩-inj    : ∀ {C} {p q : C ⇒ A} {r : f ∘ p ≈ g ∘ p} {s : f ∘ q ≈ g ∘ q}
               -> ⟨ p ⟩∣ r ∣ ≈ ⟨ q ⟩∣ s ∣ -> p ≈ q
    .universal : ∀ {C} {u : C ⇒ Ob} {p : C ⇒ A}
               -> (r : ι ∘ u ≈ p) -> ⟨ p ⟩∣ r ⌈ ∘²-resp-≈ʳ comm ⌉ʳ r ∣ ≈ u

  .η : ⟨ ι ⟩∣ _ ∣ ≈ id
  η = universal idʳ

  .∘-η : ∀ {C} {u : C ⇒ Ob} -> ⟨ ι ∘ u ⟩∣ _ ∣ ≈ u
  ∘-η = universal refl

  .ι-⟨⟩ : ∀ {C} {p : C ⇒ A} {r : f ∘ p ≈ g ∘ p} -> ι ∘ ⟨ p ⟩∣ r ∣ ≈ p
  ι-⟨⟩ = ⟨⟩-inj ∘-η

  .⟨⟩-∘ : ∀ {C D} {q : D ⇒ A} {p : C ⇒ D} {s : f ∘ q ≈ g ∘ q}
        -> ⟨ q ∘ p ⟩∣ _ ∣ ≈ ⟨ q ⟩∣ s ∣ ∘ p
  ⟨⟩-∘ = universal (∘ˡ-resp-≈ʳ ι-⟨⟩)
  
  .⟨⟩-resp-≈ : ∀ {C} {p q : C ⇒ A} {r : f ∘ p ≈ g ∘ p}
             -> (s : p ≈ q) -> ⟨ p ⟩∣ r ∣ ≈ ⟨ q ⟩∣ s ⌈ r ⌉ʳ s ∣
  ⟨⟩-resp-≈ s = universal (left ι-⟨⟩ s)

  .ι-mono : Mono ι
  ι-mono = λ r -> right (universal r) ∘-η

Equalizers = ∀ {A B} {f g : A ⇒ B} -> Equalizer f g
