open import Categories.Category

module Categories.Morphism.Square {α β γ} (C : Category α β γ) where

-- Alternatively we could write

-- open import Categories.Functor
-- open import Categories.Morphism.SquareOver (idᶠ {C = C}) (idᶠ {C = C}) public

open Category C

infix  3 _⇒ₛ_
infixr 9 _∘ₛ_
infix  4 _≈ₛ_

_⇒ₛ_ : ∀ {A B C D} -> A ⇒ B -> C ⇒ D -> Set (β ⊔ γ)
f₁ ⇒ₛ g₂ = ∃₂ λ f₂ g₁ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

idₛ : ∀ {A B} {f : A ⇒ B} -> f ⇒ₛ f
idₛ = id , id , left idˡ idʳ

_∘ₛ_ : ∀ {A B C D E F} {f : A ⇒ B} {g : C ⇒ D} {h : E ⇒ F}
     -> g ⇒ₛ h -> f ⇒ₛ g -> f ⇒ₛ h
_∘ₛ_ = zip _∘_ (zip _∘_ (λ p q -> ∘²-resp-≈ˡ q ⋯ ∘ʳ-resp-≈ʳ p))

setoidₛ : ∀ {A B C D} -> ISetoid₂ (_⇒ₛ_ {A} {B} {C} {D}) γ
setoidₛ = comapⁱˢ (λ{ (f₁ , g₂ , _) -> f₁ , g₂ }) (setoid ×ⁱˢ₂ setoid)

_≈ₛ_ : ∀ {A B C D} {f : A ⇒ B} {g : C ⇒ D} -> f ⇒ₛ g -> f ⇒ₛ g -> Set γ
_≈ₛ_ = _≈₀_
  where open ISetoid setoidₛ renaming (_≈_ to _≈₀_)
