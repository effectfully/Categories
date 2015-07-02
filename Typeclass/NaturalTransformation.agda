module Categories.Typeclass.NaturalTransformation where

open import Categories.Typeclass.Category
open import Categories.Typeclass.Functor

record IsNaturalTransformation
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂} {Ψ₀ Φ₀ : Obj₁ -> Obj₂}
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}}
  (Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀) (Ψ : IsFunctor _⇒₁_ _⇒₂_ Φ₀) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where

  open IsCategory {{...}}

  field
    η    : ∀ {O} -> Ψ₀ O ⇒₂ Φ₀ O
    comm : ∀ {A B} {f : A ⇒₁ B} -> η ∘ F₁ f ≈ F₁ f ∘ η
open IsNaturalTransformation {{...}} public

Id : ∀
  {α₁ α₂ β₁ β₂} {Obj₁ : Set α₁} {Obj₂ : Set α₂}
  {_⇒₁_ : Obj₁ -> Obj₁ -> Set β₁} {_⇒₂_ : Obj₂ -> Obj₂ -> Set β₂} {Ψ₀ : Obj₁ -> Obj₂}
  {{setoid₁ : ∀ {A B} -> Setoid (A ⇒₁ B)}} {{setoid₂ : ∀ {A B} -> Setoid (A ⇒₂ B)}}
  {{C₁ : IsCategory _⇒₁_}} {{C₂ : IsCategory _⇒₂_}}
  -> (Ψ : IsFunctor _⇒₁_ _⇒₂_ Ψ₀) -> IsNaturalTransformation Ψ Ψ
Id {{setoid₂ = setoid₂}} {{C₂ = C₂}} Ψ = record
  { η    = λ {O}         -> id
  ; comm = λ {A} {B} {f} -> let open EqReasoning setoid₂ in
    id ∘ F₁ f ≈⟨ idˡ ⟩
    F₁ f      ≈⟨ sym (F₁ f ∘ id) idʳ ⟩
    F₁ f ∘ id ∎
  } where open IsCategory C₂
