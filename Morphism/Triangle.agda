open import Categories.Category

module Categories.Morphism.Triangle {α β γ} (ℂ : Category α β γ) where

open Category ℂ

infix  3 _⇒ₜ_
infixr 9 _∘ₜ_

_⇒ₜ_ : ∀ {A B C} -> A ⇒ C -> B ⇒ C -> Set (β ⊔ γ)
h ⇒ₜ g = ∃ λ f -> g ∘ f ≈ h

idₜ : ∀ {A B} {f : A ⇒ B} -> f ⇒ₜ f
idₜ = id , idʳ

_∘ₜ_ : ∀ {A B C D} {h : A ⇒ D} {g : B ⇒ D} {f : C ⇒ D}
     -> g ⇒ₜ f -> h ⇒ₜ g -> h ⇒ₜ f
_∘ₜ_ = zip _∘_ (trans ∘′ ∘ˡ-resp-≈ʳ)
