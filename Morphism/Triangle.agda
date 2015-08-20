open import Categories.Category

module Categories.Morphism.Triangle {α β γ} (C : Category α β γ) {-A-} where

open Category C

infix  3 _⇒ₜ_
infixr 9 _∘ₜ_
infix  4 _≈ₜ_

_⇒ₜ_ : ∀ {A B C} -> A ⇒ C -> B ⇒ C -> Set (β ⊔ γ)
h ⇒ₜ g = ∃ λ f -> g ∘ f ≈ h

idₜ : ∀ {A B} {f : A ⇒ B} -> f ⇒ₜ f
idₜ = id , idʳ

_∘ₜ_ : ∀ {A B C D} {h : A ⇒ D} {g : B ⇒ D} {f : C ⇒ D}
     -> g ⇒ₜ f -> h ⇒ₜ g -> h ⇒ₜ f
_∘ₜ_ = zip _∘_ (trans ∘′ ∘ˡ-resp-≈ʳ)

setoidₜ : ∀ {A B C} -> ISetoid₂ (_⇒ₜ_ {A} {B} {C}) γ
setoidₜ = comapⁱˢ proj₁ setoid

_≈ₜ_ : ∀ {A B C} {h : A ⇒ C} {g : B ⇒ C} -> h ⇒ₜ g -> h ⇒ₜ g -> Set γ
_≈ₜ_ = _≈₀_
  where open ISetoid setoidₜ renaming (_≈_ to _≈₀_)
