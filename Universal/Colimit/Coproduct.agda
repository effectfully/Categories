open import Categories.Category

module Categories.Universal.Colimit.Coproduct {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open Category ℂ

record Coproduct (A B : Obj) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↓_

  field
    Ob  : Obj
    ι₁  : A ⇒ Ob
    ι₂  : B ⇒ Ob
    _↓_ : ∀ {C} -> A ⇒ C -> B ⇒ C -> Ob ⇒ C

    ↓-inj     : ∀ {C} {f₁ f₂ : A ⇒ C} {g₁ g₂ : B ⇒ C}
              -> f₁ ↓ g₁ ≈ f₂ ↓ g₂ -> f₁ ≈ f₂ × g₁ ≈ g₂
    universal : ∀ {C} {f : A ⇒ C} {g : B ⇒ C} {u : Ob ⇒ C}
              -> u ∘ ι₁ ≈ f -> u ∘ ι₂ ≈ g -> f ↓ g ≈ u

  η : ι₁ ↓ ι₂ ≈ id
  η = universal idˡ idˡ

  ∘-η : ∀ {C} {u : Ob ⇒ C} -> u ∘ ι₁ ↓ u ∘ ι₂ ≈ u
  ∘-η = universal refl refl

  ↓-ι₁ : ∀ {C} {f : A ⇒ C} {g : B ⇒ C} -> (f ↓ g) ∘ ι₁ ≈ f
  ↓-ι₁ = proj₁ (↓-inj ∘-η)

  ↓-ι₂ : ∀ {C} {f : A ⇒ C} {g : B ⇒ C} -> (f ↓ g) ∘ ι₂ ≈ g
  ↓-ι₂ = proj₂ (↓-inj ∘-η)

  ↓-∘ : ∀ {C D} {f : A ⇒ C} {g : B ⇒ C} {h : C ⇒ D} -> (h ∘ f) ↓ (h ∘ g) ≈ h ∘ (f ↓ g)
  ↓-∘ = universal (∘ˡ-resp-≈ˡ ↓-ι₁) (∘ˡ-resp-≈ˡ ↓-ι₂)

  ↓-resp-≈ : ∀ {C} {f₁ f₂ : A ⇒ C} {g₁ g₂ : B ⇒ C}
           -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> f₁ ↓ g₁ ≈ f₂ ↓ g₂
  ↓-resp-≈ p q = universal (left ↓-ι₁ p) (left ↓-ι₂ q)
