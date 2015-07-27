module Categories.2-Category where

open import Categories.Category
open import Categories.Functor
open import Categories.Categories.Discrete

record 2-Category α β γ δ : Set (suc (α ⊔ β ⊔ γ ⊔ δ)) where
  infix  3 _⇒_
  infixr 9 _∘_

  field
    Obj  : Set α
    _⇒_  : Obj -> Obj -> Category β γ δ
    id   : ∀ {A} -> Functor One (A ⇒ A)
    comp : ∀ {A B C} -> Bifunctor (B ⇒ C) (A ⇒ B) (A ⇒ C)

  _∘_ : ∀ {A B C} {C₁ C₂ : Category β γ δ}
      -> Functor C₁ (B ⇒ C) -> Functor C₂ (A ⇒ B) -> Bifunctor C₁ C₂ (A ⇒ C)
  F₁ ∘ F₂ = comp ∘ᶠ (F₁ ⁂ F₂)

  open ISetoid Functor-ISetoid

--  field
--    idˡ idʳ assoc
