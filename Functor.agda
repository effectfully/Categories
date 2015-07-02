module Categories.Functor where

open import Categories.Category

record Functor {α₁ α₂ β₁ β₂ γ₁ γ₂} (C₁ : Category α₁ β₁ γ₁) (C₂ : Category α₂ β₂ γ₂)
               : Set (suc (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂)) where
  private module ₁ = Category C₁; module ₂ = Category C₂
  
  field
    F₀ : ₁.Obj -> ₂.Obj
    F₁ : ∀ {A B} -> A ₁.⇒ B -> F₀ A ₂.⇒ F₀ B

    F-id     : ∀ {A} -> F₁ {A} ₁.id ₂.≈ ₂.id
    F-∘      : ∀ {A B C} {g : B ₁.⇒ C} {f : A ₁.⇒ B} -> F₁ (g ₁.∘ f) ₂.≈ F₁ g ₂.∘ F₁ f
    F-resp-≡ : ∀ {A B} {g f : A ₁.⇒ B} -> g ₁.≈ f -> F₁ g ₂.≈ F₁ f

  Functorᵒᵖ : Functor ₁.categoryᵒᵖ ₂.categoryᵒᵖ
  Functorᵒᵖ = record
    { F₀       = F₀
    ; F₁       = F₁
    ; F-id     = F-id
    ; F-∘      = F-∘
    ; F-resp-≡ = F-resp-≡
    }

Endofunctor : ∀ {α β γ} -> Category α β γ -> Set (suc (α ⊔ β ⊔ γ))
Endofunctor C = Functor C C
