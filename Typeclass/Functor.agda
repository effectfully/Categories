module Categories.Typeclass.Functor where

open import Categories.Typeclass.Category

record IsFunctor
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  (_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁) (_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂) (F₀ : Obj₁ -> Obj₂)
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}} : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  field
    F₁ : ∀ {A B} -> A ⇒₁ B -> F₀ A ⇒₂ F₀ B

    F-id     : ∀ {A} -> F₁ {A} id ≈ id
    F-∘      : ∀ {A B C} {g : B ⇒₁ C} {f : A ⇒₁ B} -> F₁ (g ∘ f) ≈ F₁ g ∘ F₁ f
    F-resp-≈ : ∀ {A B} {f g : A ⇒₁ B} -> f ≈ g -> F₁ f ≈ F₁ g

  functorᵒᵖ : IsFunctor (flip _⇒₁_) (flip _⇒₂_) F₀ {{C₁ = isCategoryᵒᵖ}} {{C₂ = isCategoryᵒᵖ}}
  functorᵒᵖ = record
    { F₁       = F₁
    ; F-id     = F-id
    ; F-∘      = F-∘
    ; F-resp-≈ = F-resp-≈
    }
open IsFunctor {{...}} public

IsEndofunctor : ∀ {α β} {Obj : Set α}
              -> (_⇒_ : Obj -> Obj -> Set β)
              -> (F₀ : Obj -> Obj) {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}}
                 {{isCategory : IsCategory _⇒_}}
              -> Set (α ⊔ β)
IsEndofunctor _⇒_ F₀ = IsFunctor _⇒_ _⇒_ F₀

record Functor {α₁ α₂ β₁ β₂} (C₁ : Category α₁ β₁) (C₂ : Category α₂ β₂)
               : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  private module C₁ = Category C₁; module C₂ = Category C₂
  field
    F₀        : C₁.Obj -> C₂.Obj
    isFunctor : IsFunctor _ _ F₀ {{C₁ = C₁.isCategory}} {{C₂ = C₂.isCategory}}

Endofunctor : ∀ {α β} -> Category α β -> Set (α ⊔ β)
Endofunctor C = Functor C C
