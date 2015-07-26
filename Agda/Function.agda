module Categories.Agda.Function where

open import Level

open import Categories.Setoid

record Π {α β γ δ} {A : Set α} {B : A -> Set β}
         (setoid : Setoid A γ) (hsetoid : HSetoid B δ) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  open Setoid¹ setoid; open HSetoid² hsetoid

  infixl 5 _⟨$⟩_

  field
    ⟨_⟩  : ∀ x -> B x
    cong : ∀ {x y} -> x ≈₁ y -> ⟨ x ⟩ ≈₂ ⟨ y ⟩

  _⟨$⟩_ = ⟨_⟩
open Π using (_⟨$⟩_)

_─>_ : ∀ {α β γ δ} {A : Set α} {B : Set β} -> Setoid A γ -> Setoid B δ -> Set (α ⊔ β ⊔ γ ⊔ δ)
setoid₁ ─> setoid₂ = Π setoid₁ hsetoid
  where open Indexed setoid₂; open Hetero isetoid

Injective : ∀ {α β γ δ} {A : Set α} {B : Set β}
              {setoid₁ : Setoid A γ} {setoid₂ : Setoid B δ}
          -> setoid₁ ─> setoid₂ -> Set (α  ⊔ γ ⊔ δ)
Injective {setoid₁ = setoid₁} {setoid₂ = setoid₂} f = ∀ {x y} -> f ⟨$⟩ x ≈₂ f ⟨$⟩ y -> x ≈₁ y
  where open Setoid¹ setoid₁; open Setoid² setoid₂
