open import Categories.Category

module Categories.Morphism.Morphism {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Mono {A B} (f : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field mono : ∀ {C} {g h : C ⇒ A} -> f ∘ g ≈ f ∘ h -> g ≈ h

record Epi  {A B} (f : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field epi  : ∀ {C} {g h : B ⇒ C} -> g ∘ f ≈ h ∘ f -> g ≈ h

record Iso  {A B} (f : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field
    f⁻¹  : B ⇒ A
    isoˡ : f ∘ f⁻¹ ≈ id
    isoʳ : f⁻¹ ∘ f ≈ id

record _≃_ A B : Set (α ⊔ β ⊔ γ) where
  field
    {f} : A ⇒ B
    iso : Iso f
