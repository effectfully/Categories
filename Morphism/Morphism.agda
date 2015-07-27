open import Categories.Category

module Categories.Morphism.Morphism {α β γ} (ℂ : Category α β γ) where

open Category ℂ

Mono : ∀ {A B} -> A ⇒ B -> Set (α ⊔ β ⊔ γ)
Mono {A = A} f = ∀ {C} {g h : C ⇒ A} -> .(f ∘ g ≈ f ∘ h) -> g ≈ h

Epi  : ∀ {A B} -> A ⇒ B -> Set (α ⊔ β ⊔ γ)
Epi  {B = B} f = ∀ {C} {g h : B ⇒ C} -> .(g ∘ f ≈ h ∘ f) -> g ≈ h

record Iso  {A B} (f : A ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field
    f⁻¹  : B ⇒ A
    isoˡ : f ∘ f⁻¹ ≈ id
    isoʳ : f⁻¹ ∘ f ≈ id

record _≃_ A B : Set (α ⊔ β ⊔ γ) where
  field
    {f} : A ⇒ B
    iso : Iso f
