open import Categories.Category

module Categories.Universal.Limit.Equalizer {α β γ} (ℂ : Category α β γ) where

open Category ℂ

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
  ∘-η = universal irefl

  ι-↙ : ∀ {C} {p : C ⇒ A} -> ι ∘ (↙ p) ≈ p
  ι-↙ = ↙-inj ∘-η
    
  ↙-resp-≈ : ∀ {C} {p q : C ⇒ A} -> p ≈ q -> ↙ p ≈ ↙ q
  ↙-resp-≈ r = universal (itrans ι-↙ (isym r))
