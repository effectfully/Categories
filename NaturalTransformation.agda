module Categories.NaturalTransformation where

open import Categories.Category
open import Categories.Functor

record NaturalTransformation {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                             (Ψ Φ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  private module ₁ = Category C₁; module ₂ = Category C₂
  open Functor Ψ renaming (F₀ to Ψ₀; F₁ to Ψ₁)
  open Functor Φ renaming (F₀ to Φ₀; F₁ to Φ₁)
  
  field
    η    : ∀ O -> Ψ₀ O ₂.⇒ Φ₀ O
    comm : ∀ {A B} {f : A ₁.⇒ B} -> η _ ₂.∘ Ψ₁ f ₂.≈ Φ₁ f ₂.∘ η _
open NaturalTransformation public

-- Id : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
--    -> (Ψ : Functor C₁ C₂) -> NaturalTransformation Ψ Ψ
-- Id {C₁ = C₁} {C₂ = C₂} Ψ = record
--   { η    = λ _ -> Category.id C₂
--   ; comm = λ {A} {B} {f} -> {!f!}
--   } where open Category C₁; open Category C₂
