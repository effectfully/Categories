module Categories.Category where

open import Level public
open import Function as F using (flip) public

record IsEquivalence {α β} {A : Set α} (_≈_ : A -> A -> Set β) : Set (α ⊔ β) where
  field
    refl  : ∀ {x}     -> x ≈ x
    sym   : ∀ {x y}   -> x ≈ y -> y ≈ x
    trans : ∀ {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

record Category α β γ : Set (suc (α ⊔ β ⊔ γ)) where
  infix  3 _⇒_
  infix  4 _≈_
  infixr 9 _∘_

  field
    Obj           : Set α
    _⇒_           : Obj -> Obj -> Set β
    _≈_           : ∀ {A B} -> A ⇒ B -> A ⇒ B -> Set γ
    isEquivalence : ∀ {A B} -> IsEquivalence (_≈_ {A} {B})

    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    idˡ      : ∀ {A B} {f : A ⇒ B} -> id ∘ f ≈ f
    idʳ      : ∀ {A B} {f : A ⇒ B} -> f ∘ id ≈ f
    assoc    : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}
             -> (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    ∘-resp-≈ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
             -> g₁ ≈ g₂ -> f₁ ≈ f₂ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

  open module Equivalence {A B} = IsEquivalence (isEquivalence {A} {B})

  categoryᵒᵖ : Category α β γ
  categoryᵒᵖ = record 
    { _⇒_           = flip _⇒_
    ; isEquivalence = isEquivalence
    ; id            = id
    ; _∘_           = flip _∘_
    ; idˡ           = idʳ
    ; idʳ           = idˡ
    ; assoc         = sym assoc
    ; ∘-resp-≈      = flip ∘-resp-≈
    }

  _[_⇒_] = _⇒_
  _[_≈_] = _≈_
  _[_∘_] = _∘_
open Category public
