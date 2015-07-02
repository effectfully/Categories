module Categories.FunctorCategory where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

FunctorCategory : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂}
                -> Category α₁ β₁ γ₁
                -> Category α₂ β₂ γ₂
                -> Category (suc (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂))
                            (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂)
                            {!!}
FunctorCategory C₁ C₂ = record
  { Obj           = Functor C₁ C₂
  ; _⇒_           = NaturalTransformation
  ; _≈_           = λ Η₁ Η₂ -> ∀ O -> C₂ [ η Η₁ O ≈ η Η₂ O ]
  ; isEquivalence = record
    { refl  = λ     O -> refl
    ; sym   = λ p   O -> sym   (p O)
    ; trans = λ p q O -> trans (p O) (q O)
    }
  ; id            = {!!}
  ; _∘_           = {!!}
  ; idˡ           = {!!}
  ; idʳ           = {!!}
  ; assoc         = {!!}
  ; ∘-resp-≈      = {!!}
  } where open Equivalence C₂
