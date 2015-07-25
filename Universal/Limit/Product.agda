open import Categories.Category

module Categories.Universal.Limit.Product {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open Category ℂ

record Product (A B : Obj) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↑_

  field
    Ob  : Obj
    π₁  : Ob ⇒ A
    π₂  : Ob ⇒ B
    _↑_ : ∀ {C} -> C ⇒ A -> C ⇒ B -> C ⇒ Ob

    ↑-inj    : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
             -> f₁ ↑ g₁ ≈ f₂ ↑ g₂ -> f₁ ≈ f₂ × g₁ ≈ g₂
    universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {u : C ⇒ Ob}
              -> π₁ ∘ u ≈ f -> π₂ ∘ u ≈ g -> f ↑ g ≈ u

  η : π₁ ↑ π₂ ≈ id
  η = universal idʳ idʳ

  ∘-η : ∀ {C} {u : C ⇒ Ob} -> π₁ ∘ u ↑ π₂ ∘ u ≈ u
  ∘-η = universal refl refl

  π₁-↑ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π₁ ∘ (f ↑ g) ≈ f
  π₁-↑ = proj₁ (↑-inj ∘-η)

  π₂-↑ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π₂ ∘ (f ↑ g) ≈ g
  π₂-↑ = proj₂ (↑-inj ∘-η)

  ↑-∘ : ∀ {C D} {f : D ⇒ A} {g : D ⇒ B} {h : C ⇒ D} -> (f ∘ h) ↑ (g ∘ h) ≈ (f ↑ g) ∘ h
  ↑-∘ = universal (∘ˡ-resp-≈ʳ π₁-↑) (∘ˡ-resp-≈ʳ π₂-↑)

  ↑-resp-≈ : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
           -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> f₁ ↑ g₁ ≈ f₂ ↑ g₂
  ↑-resp-≈ p q = universal (left π₁-↑ p) (left π₂-↑ q)
