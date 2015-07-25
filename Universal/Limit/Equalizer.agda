open import Categories.Category

module Categories.Universal.Limit.Equalizer {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism.Morphism

open IndexedEqReasoningWith ℂ

record Equalizer {A B : Obj} (f g : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  infixr 5 ↙_

  field
    Ob : Obj
    ι  : Ob ⇒ A
    ↙_ : ∀ {C} -> C ⇒ A -> C ⇒ Ob
      
    comm      : f ∘ ι ≈ g ∘ ι
    ↙-inj     : ∀ {C} {p q : C ⇒ A} -> ↙ p ≈ ↙ q -> p ≈ q
    universal : ∀ {C} {p : C ⇒ A} {u : C ⇒ Ob} -> ι ∘ u ≈ p -> ↙ p ≈ u

  η : ↙ ι ≈ id
  η = universal idʳ

  ∘-η : ∀ {C} {u : C ⇒ Ob} -> ↙ (ι ∘ u) ≈ u
  ∘-η = universal refl

  ι-↙ : ∀ {C} {p : C ⇒ A} -> ι ∘ (↙ p) ≈ p
  ι-↙ = ↙-inj ∘-η

  ↙-∘ : ∀ {C D} {q : D ⇒ A} {p : C ⇒ D} -> ↙ (q ∘ p) ≈ (↙ q) ∘ p
  ↙-∘ = universal (∘ˡ-resp-≈ʳ ι-↙)
  
  ↙-resp-≈ : ∀ {C} {p q : C ⇒ A} -> p ≈ q -> ↙ p ≈ ↙ q
  ↙-resp-≈ r = universal (left ι-↙ r)

  ι-mono : Mono ℂ ι
  ι-mono = record
    { mono = λ {_ p q} r ->
        begin
          p         ←⟨ universal r ⟩
          ↙ (ι ∘ q) →⟨ ∘-η         ⟩
          q
        ∎
    }
