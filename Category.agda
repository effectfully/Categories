module Categories.Category where

open import Level public
open import Function using (flip; _∘′_) renaming (id to id→) public
open import Data.Product using (_,_) public

open import Categories.Setoid public

record Category α β γ : Set (suc (α ⊔ β ⊔ γ)) where
  infix  3 _⇒_
  infixr 9 _∘_
  
  field
    Obj    : Set α
    _⇒_    : Obj -> Obj -> Set β
    setoid : IndexedSetoid₂ _⇒_ γ

  open IndexedSetoid setoid public

  field
    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    idˡ      : ∀ {A B} {f : A ⇒ B} -> id ∘ f ≈ f
    idʳ      : ∀ {A B} {f : A ⇒ B} -> f ∘ id ≈ f
    assoc    : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}
             -> (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    ∘-resp-≈ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
             -> g₁ ≈ g₂ -> f₁ ≈ f₂ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

  -- assocₑ : ∀ {A B C D} (h : C ⇒ D) {g : B ⇒ C} {f : A ⇒ B}
  --        -> (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
  -- assocₑ _ = assoc

  ∘-resp-≈ˡ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f : A ⇒ B} -> g₁ ≈ g₂ -> g₁ ∘ f ≈ g₂ ∘ f
  ∘-resp-≈ˡ p = ∘-resp-≈ p irefl

  ∘-resp-≈ʳ : ∀ {A B C} {g : B ⇒ C} {f₁ f₂ : A ⇒ B} -> f₁ ≈ f₂ -> g ∘ f₁ ≈ g ∘ f₂
  ∘-resp-≈ʳ p = ∘-resp-≈ irefl p

module _ {α β γ} (C : Category α β γ) where
  open Category C

  module IndexedSetoidFrom      = IndexedSetoid setoid
  module IndexedEqReasoningFrom = IndexedEqReasoning setoid

  module Heterogeneous where
    open Hetero setoid public

    ∘-resp-≋ : ∀ {A A' B B' C C'} {g₁ : B ⇒ C} {g₂ : B' ⇒ C'} {f₁ : A ⇒ B} {f₂ : A' ⇒ B'}
             -> g₁ ≋ g₂ -> f₁ ≋ f₂ -> g₁ ∘ f₁ ≋ g₂ ∘ f₂
    ∘-resp-≋ (hetero g₁≈g₂) (hetero f₁≈f₂) = hetero (∘-resp-≈ g₁≈g₂ f₁≈f₂)

  module MixedEqReasoningFrom where
    open Heterogeneous public; open MixedEqReasoning setoid public

module IndexedEqReasoningWith {α β γ} (C : Category α β γ) where
  open Category C public; open IndexedEqReasoning setoid public

module _ {α β γ} (C : Category α β γ) where
  module First  where
    open Category C renaming (Obj to Obj₁; _⇒_ to _⇒₁_; id to id₁; _∘_ to _∘₁_;
                              idˡ to idˡ₁; idʳ to idʳ₁; assoc to assoc₁; ∘-resp-≈ to ∘-resp-≈₁;
                              _≈_ to _≈₁_; irefl to irefl₁; isym to isym₁; itrans to itrans₁) public
    open Heterogeneous C renaming (_≋_ to _≋₁_; hetero to hetero₁; ∘-resp-≋ to ∘-resp-≋₁) public

  module Second where
    open Category C renaming (Obj to Obj₂; _⇒_ to _⇒₂_; id to id₂; _∘_ to _∘₂_;
                              idˡ to idˡ₂; idʳ to idʳ₂; assoc to assoc₂; ∘-resp-≈ to ∘-resp-≈₂;
                              _≈_ to _≈₂_; irefl to irefl₂; isym to isym₂; itrans to itrans₂) public
    open Heterogeneous C renaming (_≋_ to _≋₂_; hetero to hetero₂; ∘-resp-≋ to ∘-resp-≋₂) public

  module Third  where
    open Category C renaming (Obj to Obj₃; _⇒_ to _⇒₃_; id to id₃; _∘_ to _∘₃_;
                              idˡ to idˡ₃; idʳ to idʳ₃; assoc to assoc₃; ∘-resp-≈ to ∘-resp-≈₃;
                              _≈_ to _≈₃_; irefl to irefl₃; isym to isym₃; itrans to itrans₃) public
    open Heterogeneous C renaming (_≋_ to _≋₃_; hetero to hetero₃; ∘-resp-≋ to ∘-resp-≋₃) public

module _ where
  open Category

  arr-syntax  = _⇒_
  eq-syntax   = _≈_
  comp-syntax = _∘_
  heq-syntax  = Heterogeneous._≋_

  syntax arr-syntax  C A B = A [ C ]⇒ B
  syntax eq-syntax   C f g = f [ C ]≈ g
  syntax comp-syntax C f g = f [ C ]∘ g
  syntax heq-syntax  C f g = f [ C ]≋ g

_ᵒᵖ : ∀ {α β γ} -> Category α β γ -> Category α β γ
C ᵒᵖ = record 
  { _⇒_      = flip _⇒_
  ; setoid   = record
      { _≈_                  = _≈_
      ; isIndexedEquivalence = record
          { irefl  = irefl
          ; isym   = isym
          ; itrans = itrans
          }
      }
  ; id       = id
  ; _∘_      = flip _∘_
  ; idˡ      = idʳ
  ; idʳ      = idˡ
  ; assoc    = isym assoc
  ; ∘-resp-≈ = flip ∘-resp-≈
  } where open Category C
