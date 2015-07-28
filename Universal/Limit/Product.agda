open import Categories.Category

module Categories.Universal.Limit.Product {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open Category ℂ

record Product (A B : Obj) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↑_

  field
    Ob  : Obj
    π¹  : Ob ⇒ A
    π²  : Ob ⇒ B
    _↑_ : ∀ {C} -> C ⇒ A -> C ⇒ B -> C ⇒ Ob

    ↑-inj    : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
             -> f₁ ↑ g₁ ≈ f₂ ↑ g₂ -> f₁ ≈ f₂ × g₁ ≈ g₂
    universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {u : C ⇒ Ob}
              -> π¹ ∘ u ≈ f -> π² ∘ u ≈ g -> f ↑ g ≈ u

  η : π¹ ↑ π² ≈ id
  η = universal idʳ idʳ

  ∘-η : ∀ {C} {u : C ⇒ Ob} -> π¹ ∘ u ↑ π² ∘ u ≈ u
  ∘-η = universal refl refl

  π¹-↑ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π¹ ∘ (f ↑ g) ≈ f
  π¹-↑ = proj₁ (↑-inj ∘-η)

  π²-↑ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π² ∘ (f ↑ g) ≈ g
  π²-↑ = proj₂ (↑-inj ∘-η)

  ↑-∘ : ∀ {C D} {f : D ⇒ A} {g : D ⇒ B} {h : C ⇒ D} -> (f ∘ h) ↑ (g ∘ h) ≈ (f ↑ g) ∘ h
  ↑-∘ = universal (∘ˡ-resp-≈ʳ π¹-↑) (∘ˡ-resp-≈ʳ π²-↑)

  ↑-resp-≈ : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
           -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> f₁ ↑ g₁ ≈ f₂ ↑ g₂
  ↑-resp-≈ p q = universal (left π¹-↑ p) (left π²-↑ q)

BinaryProducts = ∀ {A B} -> Product A B
