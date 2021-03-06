open import Categories.Category

module Categories.Object.Colimit.Coequalizer {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism ℂ

open Category ℂ

record Coequalizer {A B} (f g : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field
    Ob     : Obj
    π      : B ⇒ Ob
    [_]∣_∣ : ∀ {C} -> (p : B ⇒ C) -> .(p ∘ f ≈ p ∘ g) -> Ob ⇒ C
    
    .π-comm  : π ∘ f ≈ π ∘ g
    .[]-inj  : ∀ {C} {p q : B ⇒ C} {r : p ∘ f ≈ p ∘ g} {s : q ∘ f ≈ q ∘ g}
             -> [ p ]∣ r ∣ ≈ [ q ]∣ s ∣ -> p ≈ q
    .[]-univ : ∀ {C} {p : B ⇒ C} {u : Ob ⇒ C}
             -> (r : u ∘ π ≈ p) -> [ p ]∣ r ⌈ ∘²-resp-≈ˡ π-comm ⌉ˡ r ∣ ≈ u

  .η : [ π ]∣ _ ∣ ≈ id
  η = []-univ idˡ

  .∘-η : ∀ {C} {u : Ob ⇒ C} -> [ u ∘ π ]∣ _ ∣ ≈ u
  ∘-η = []-univ refl

  .[]-π : ∀ {C} {p : B ⇒ C} {r : p ∘ f ≈ p ∘ g} -> [ p ]∣ r ∣ ∘ π ≈ p
  []-π = []-inj ∘-η

  .∘-[] : ∀ {C D} {q : C ⇒ D} {p : B ⇒ C} {r : p ∘ f ≈ p ∘ g}
        -> [ q ∘ p ]∣ _ ∣ ≈ q ∘ [ p ]∣ r ∣
  ∘-[] = []-univ (∘ˡ-resp-≈ˡ []-π)

  .[]-resp-≈ : ∀ {C} {p q : B ⇒ C} {r : p ∘ f ≈ p ∘ g}
             -> (s : p ≈ q) -> [ p ]∣ r ∣ ≈ [ q ]∣ s ⌈ r ⌉ˡ s ∣
  []-resp-≈ r = []-univ (left []-π r)

  .π-epi : Epi π
  π-epi = λ r -> right ([]-univ r) ∘-η

Coequalizers = ∀ {A B} -> (f g : A ⇒ B) -> Coequalizer f g
