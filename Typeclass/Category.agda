module Categories.Typeclass.Category where

open import Level public
open import Function as F using (flip) public

record IsEquivalence {α} {A : Set α} (_≈_ : A -> A -> Set α) : Set α where
  field
    refl  : ∀ x       -> x ≈ x
    sym   : ∀ x {y}   -> x ≈ y -> y ≈ x
    trans : ∀ x {y z} -> x ≈ y -> y ≈ z -> x ≈ z
open IsEquivalence {{...}} public

record Setoid {α} (A : Set α) : Set (suc α) where
  infix 4 _≈_

  field
    _≈_           : A -> A -> Set α
    isEquivalence : IsEquivalence _≈_
  
  instance
    Setoid->IsEquivalence : IsEquivalence _≈_
    Setoid->IsEquivalence = isEquivalence
open Setoid {{...}} public

module EqReasoning {α} {A : Set α} {{setoid : Setoid A}} where
  infixr 2 _≈⟨_⟩_
  infix  3 _∎

  _≈⟨_⟩_ : ∀ (x {y z} : A) -> x ≈ y -> y ≈ z -> x ≈ z
  x ≈⟨ p ⟩ q = trans x p q

  _∎ : (x : A) -> x ≈ x
  x ∎ = refl x
open EqReasoning public

record IsCategory
  {α β} {Obj : Set α} (_⇒_ : Obj -> Obj -> Set β)
  {{setoid : ∀ {A B} -> Setoid (A ⇒ B)}} : Set (α ⊔ β) where
  infixr 9 _∘_

  field
    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    idˡ      : ∀ {A B} {f : A ⇒ B} -> id ∘ f ≈ f
    idʳ      : ∀ {A B} {f : A ⇒ B} -> f ∘ id ≈ f
    assoc    : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}
             -> (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    ∘-resp-≈ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
             -> g₁ ≈ g₂ -> f₁ ≈ f₂ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

  isCategoryᵒᵖ : IsCategory (flip _⇒_)
  isCategoryᵒᵖ = record 
    { id       = id
    ; _∘_      = flip _∘_
    ; idˡ      = idʳ
    ; idʳ      = idˡ
    ; assoc    = sym {{isEquivalence {{setoid}}}} _ assoc
    ; ∘-resp-≈ = flip ∘-resp-≈
    }
open IsCategory {{...}} public

record Category α β : Set (suc (α ⊔ β)) where
  infix  4 _⇒_

  field
    {Obj}      : Set α
    {_⇒_}      : Obj -> Obj -> Set β
    setoid     : ∀ {A B} -> Setoid (A ⇒ B)
    isCategory : IsCategory _⇒_

  instance
    Category->Setoid : ∀ {A B} -> Setoid (A ⇒ B)
    Category->Setoid = setoid

    Category->IsCategory : IsCategory _⇒_
    Category->IsCategory = isCategory

  categoryᵒᵖ : Category α β
  categoryᵒᵖ = record
    { setoid     = setoid
    ; isCategory = isCategoryᵒᵖ
    }
