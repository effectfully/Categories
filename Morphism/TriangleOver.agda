open import Categories.Category
open import Categories.Functor

module Categories.Morphism.TriangleOver
  {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} (F : Functor C₁ C₂) where

open Functor F; open Category₁ C₁; open Category C₂

infix  3 _⇒ₜ_
infixr 9 _∘ₜ_
infix  4 _≈ₜ_

_⇒ₜ_ : ∀ {A B C} -> F· A ⇒ C -> F· B ⇒ C -> Set (β₁ ⊔ γ₂)
h ⇒ₜ g = ∃ λ f -> h ≈ g ∘ F⇒ f

idₜ : ∀ {A B} {h : F· A ⇒ B} -> h ⇒ₜ h
idₜ = id₁ , sym (∘-resp-≈ˡ F-id ⋯ idʳ)

_∘ₜ_ : ∀ {A B C D} {h : F· A ⇒ D} {g : F· B ⇒ D} {f : F· C ⇒ D}
     -> g ⇒ₜ f -> h ⇒ₜ g -> h ⇒ₜ f
_∘ₜ_ = zip _∘₁_ (λ p q -> q ⋯ left (∘ʳ-resp-≈ʳ p) (∘-resp-≈ˡ F-∘))

setoidₜ : ∀ {A B C} -> ISetoid₂ (_⇒ₜ_ {A} {B} {C}) γ₁
setoidₜ = comapⁱˢ proj₁ setoid₁

_≈ₜ_ : ∀ {A B C} {h : F· A ⇒ C} {g : F· B ⇒ C} -> h ⇒ₜ g -> h ⇒ₜ g -> Set γ₁
_≈ₜ_ = _≈₀_
  where open ISetoid setoidₜ renaming (_≈_ to _≈₀_)
