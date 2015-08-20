open import Categories.Category

module Categories.Morphism.Triangle {α β γ} (C : Category α β γ) where

-- Alternatively we can write

-- open import Categories.Functor
-- open import Categories.Morphism.TriangleOver (idᶠ {C = C}) public

open Category C

infix  3 _⇒ₜ_
infixr 9 _∘ₜ_
infix  4 _≈ₜ_

_⇒ₜ_ : ∀ {A B C} -> A ⇒ C -> B ⇒ C -> Set (β ⊔ γ)
h ⇒ₜ g = ∃ λ f -> h ≈ g ∘ f

idₜ : ∀ {A B} {h : A ⇒ B} -> h ⇒ₜ h
idₜ = id , sym idʳ

_∘ₜ_ : ∀ {A B C D} {h : A ⇒ D} {g : B ⇒ D} {f : C ⇒ D}
     -> g ⇒ₜ f -> h ⇒ₜ g -> h ⇒ₜ f
_∘ₜ_ = zip _∘_ (λ p q -> q ⋯ ∘ʳ-resp-≈ʳ p)

setoidₜ : ∀ {A B C} -> ISetoid₂ (_⇒ₜ_ {A} {B} {C}) γ
setoidₜ = comapⁱˢ proj₁ setoid

_≈ₜ_ : ∀ {A B C} {h : A ⇒ C} {g : B ⇒ C} -> h ⇒ₜ g -> h ⇒ₜ g -> Set γ
_≈ₜ_ = _≈₀_
  where open ISetoid setoidₜ renaming (_≈_ to _≈₀_)
