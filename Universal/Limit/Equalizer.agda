open import Categories.Category

module Categories.Universal.Limit.Equalizer {α β γ} (C : Category α β γ)  where

open import Data.Product

open Category C

record Equalizer {A B : Obj} (f g : A ⇒ B)  : Set (α ⊔ β ⊔ γ) where
  infixl 5 ↙_

  field
    Eq : Obj
    ι  : Eq ⇒ A
    ↙_ : ∀ {C} -> C ⇒ A -> C ⇒ Eq
      
    comm      : f ∘ ι ≈ g ∘ ι
    ↙-inj     : ∀ {C} {p q : C ⇒ A} -> ↙ p ≈ ↙ q -> p ≈ q
    universal : ∀ {C} {p : C ⇒ A} {u : C ⇒ Eq} -> ι ∘ u ≈ p -> ↙ p ≈ u

  η : ↙ ι ≈ id
  η = universal idʳ

  ∘-η : ∀ {C} {u : C ⇒ Eq} -> ↙ (ι ∘ u) ≈ u
  ∘-η = universal irefl

  ι-↙ : ∀ {C} {p : C ⇒ A} -> ι ∘ (↙ p) ≈ p
  ι-↙ = ↙-inj ∘-η
    
  ↙-resp-≈ : ∀ {C} {p q : C ⇒ A} -> p ≈ q -> ↙ p ≈ ↙ q
  ↙-resp-≈ r = universal (itrans ι-↙ (isym r))
