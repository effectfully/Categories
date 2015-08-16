open import Categories.Category

module Categories.Morphism.Triangle {α β γ} (ℂ : Category α β γ) where

open Category ℂ

_⇒ₜ_ : ∀ {A B C} -> A ⇒ C -> B ⇒ C -> Set (β ⊔ γ)
f ⇒ₜ g = ∃ λ h -> g ∘ h ≈ f

idₜ : ∀ {A B} {f : A ⇒ B} -> f ⇒ₜ f
idₜ = id , idʳ

_∘ₜ_ : ∀ {A B C D} {f : A ⇒ D} {g : B ⇒ D} {h : C ⇒ D} -> g ⇒ₜ h -> f ⇒ₜ g -> f ⇒ₜ h
_∘ₜ_ = zip _∘_ (trans ∘′ ∘ˡ-resp-≈ʳ)
