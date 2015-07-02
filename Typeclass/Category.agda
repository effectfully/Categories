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

module EqReasoning {α} {A : Set α} (setoid : Setoid A) where
  infix  4 _IsRelatedTo_
  infix  1 begin_
  infixr 2 _→⟨_⟩_ _←⟨_⟩_
  infix  3 _∎
  
  record _IsRelatedTo_ (x y : A) : Set α where
    constructor relTo
    field eq : x ≈ y

  begin_ : ∀ {x y} -> x IsRelatedTo y -> x ≈ y
  begin (relTo p) = p

  _→⟨_⟩_ : ∀ {y z} x -> x ≈ y -> y IsRelatedTo z -> x IsRelatedTo z
  x →⟨ p ⟩ (relTo q) = relTo (trans x p q)

  _←⟨_⟩_ : ∀ {y z} x -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  _←⟨_⟩_ {y} x p (relTo q) = relTo (trans x (sym y p) q)

  _∎ : ∀ x -> x IsRelatedTo x
  x ∎ = relTo (refl x)
open EqReasoning {{...}} public

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

  open IsCategory {{...}}

  categoryᵒᵖ : Category α β
  categoryᵒᵖ = record
    { setoid     = setoid
    ; isCategory = isCategoryᵒᵖ
    }
