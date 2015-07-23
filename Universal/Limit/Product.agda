open import Categories.Category

module Categories.Universal.Limit.Product {α β γ} (C : Category α β γ) where

open import Data.Product

open Category C

record Product (A B : Obj) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↑_

  field
    A×B : Obj
    π₁  : A×B ⇒ A
    π₂  : A×B ⇒ B
    _↑_ : ∀ {C} -> C ⇒ A -> C ⇒ B -> C ⇒ A×B

    ↑-inj    : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
             -> f₁ ↑ g₁ ≈ f₂ ↑ g₂ -> f₁ ≈ f₂ × g₁ ≈ g₂
    universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {u : C ⇒ A×B}
              -> π₁ ∘ u ≈ f -> π₂ ∘ u ≈ g -> f ↑ g ≈ u

  η : π₁ ↑ π₂ ≈ id
  η = universal idʳ idʳ

  ∘-η : ∀ {C} {u : C ⇒ A×B} -> π₁ ∘ u ↑ π₂ ∘ u ≈ u
  ∘-η = universal irefl irefl

  π₁-↑ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π₁ ∘ (f ↑ g) ≈ f
  π₁-↑ = proj₁ (↑-inj ∘-η)

  π₂-↑ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π₂ ∘ (f ↑ g) ≈ g
  π₂-↑ = proj₂ (↑-inj ∘-η)

  ↑-resp-≈ : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
           -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> f₁ ↑ g₁ ≈ f₂ ↑ g₂
  ↑-resp-≈ p q = universal (itrans π₁-↑ (isym p)) (itrans π₂-↑ (isym q))
