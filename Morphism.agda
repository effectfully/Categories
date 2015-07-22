module Categories.Morphism where

open import Data.Product

open import Categories.Category

module _ {α β γ} (C : Category α β γ) where
  open Category C

  module _ {A B : Obj} (f : A ⇒ B) where
    record Mono : Set (α ⊔ β ⊔ γ) where
      field mono : ∀ {C} {g h : C ⇒ A} -> f ∘ g ≈ f ∘ h -> g ≈ h

    record Epi  : Set (α ⊔ β ⊔ γ) where
      field epi  : ∀ {C} {g h : B ⇒ C} -> g ∘ f ≈ h ∘ f -> g ≈ h

    record Iso  : Set (α ⊔ β ⊔ γ) where
      field
        f⁻¹  : B ⇒ A
        isoˡ : f ∘ f⁻¹ ≈ id
        isoʳ : f⁻¹ ∘ f ≈ id

  record _≃_ A B : Set (α ⊔ β ⊔ γ) where
    field
      {f} : A ⇒ B
      iso : Iso f

module _ {α β} {A : Set α} {B : Set β} (f : A -> B) where
  record Injective γ δ : Set (α ⊔ β ⊔ suc (γ ⊔ δ)) where
    field
      setoid₁ : Setoid A γ
      setoid₂ : Setoid B δ

    open Firstˢ setoid₁; open Secondˢ setoid₂

    field
      inj : ∀ {x y} -> f x ≈₂ f y -> x ≈₁ y

  record Surjective δ : Set (α ⊔ β ⊔ suc δ) where
    field
      setoid : Setoid B δ

    open Setoid setoid

    field
      surj : ∀ y -> ∃ λ x -> f x ≈ y

  Bijective = λ γ δ ε -> Injective γ δ × Surjective ε
