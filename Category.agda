module Categories.Category where

open import Level public
open import Function using (flip; _∘′_; _$_; case_of_) renaming (id to id→) public
open import Data.Product using (_,_) public

open import Categories.Setoid public

record Category α β γ : Set (suc (α ⊔ β ⊔ γ)) where
  infix  3 _⇒_
  infixr 9 _∘_
  
  field
    Obj    : Set α
    _⇒_    : Obj -> Obj -> Set β
    setoid : IndexedSetoid₂ _⇒_ γ

  open IndexedSetoid setoid public; open Tools public

  field
    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    idˡ      : ∀ {A B} {f : A ⇒ B} -> id ∘ f ≈ f
    idʳ      : ∀ {A B} {f : A ⇒ B} -> f ∘ id ≈ f
    assoc    : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}
             -> (h ∘ g) ∘ f ≈ h ∘ g ∘ f
    ∘-resp-≈ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
             -> g₁ ≈ g₂ -> f₁ ≈ f₂ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

  -- assocₑ : ∀ {A B C D} (h : C ⇒ D) {g : B ⇒ C} {f : A ⇒ B}
  --        -> (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
  -- assocₑ _ = assoc

  ∘-resp-≈ˡ : ∀ {A B C} {g : B ⇒ C} {f₁ f₂ : A ⇒ B} -> f₁ ≈ f₂ -> g ∘ f₁ ≈ g ∘ f₂
  ∘-resp-≈ˡ p = ∘-resp-≈ refl p

  ∘-resp-≈ʳ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f : A ⇒ B} -> g₁ ≈ g₂ -> g₁ ∘ f ≈ g₂ ∘ f
  ∘-resp-≈ʳ p = ∘-resp-≈ p refl

  reassocˡ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
           -> (h ∘ g) ∘ f ≈ i -> h ∘ g ∘ f ≈ i
  reassocˡ = right assoc

  reassocʳ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
           -> i ≈ (h ∘ g) ∘ f -> i ≈ h ∘ g ∘ f
  reassocʳ = flip trans assoc

  reassoc² : ∀ {A B₁ B₂ C₁ C₂ D} {h₁ : C₁ ⇒ D} {h₂ : C₂ ⇒ D}
               {g₁ : B₁ ⇒ C₁} {g₂ : B₂ ⇒ C₂} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
           -> (h₁ ∘ g₁) ∘ f₁ ≈ (h₂ ∘ g₂) ∘ f₂ -> h₁ ∘ g₁ ∘ f₁ ≈ h₂ ∘ g₂ ∘ f₂
  reassoc² = assoc ⟨_⟩ assoc

  unreassocˡ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
             -> h ∘ g ∘ f ≈ i -> (h ∘ g) ∘ f ≈ i
  unreassocˡ = trans assoc

  unreassocʳ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
             -> i ≈ h ∘ g ∘ f -> i ≈ (h ∘ g) ∘ f
  unreassocʳ = flip left assoc

  unreassoc² : ∀ {A B₁ B₂ C₁ C₂ D} {h₁ : C₁ ⇒ D} {h₂ : C₂ ⇒ D}
                 {g₁ : B₁ ⇒ C₁} {g₂ : B₂ ⇒ C₂} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
             -> h₁ ∘ g₁ ∘ f₁ ≈ h₂ ∘ g₂ ∘ f₂ -> (h₁ ∘ g₁) ∘ f₁ ≈ (h₂ ∘ g₂) ∘ f₂
  unreassoc² = assoc ⟩_⟨ assoc

  ∘ˡ-resp-≈ˡ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : C ⇒ D} 
             -> g ∘ f ≈ i -> (h ∘ g) ∘ f ≈ h ∘ i
  ∘ˡ-resp-≈ˡ = unreassocˡ ∘′ ∘-resp-≈ˡ

  ∘ʳ-resp-≈ˡ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : C ⇒ D} 
             -> i ≈ g ∘ f -> h ∘ i ≈ (h ∘ g) ∘ f
  ∘ʳ-resp-≈ˡ = unreassocʳ ∘′ ∘-resp-≈ˡ

  ∘²-resp-≈ˡ : ∀ {A B C D} {h : C ⇒ D} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
             -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> (h ∘ g₁) ∘ f₁ ≈ (h ∘ g₂) ∘ f₂
  ∘²-resp-≈ˡ = unreassoc² ∘′ ∘-resp-≈ˡ

  ∘ˡ-resp-≈ʳ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : D ⇒ A}
             -> g ∘ f ≈ i -> g ∘ f ∘ h ≈ i ∘ h
  ∘ˡ-resp-≈ʳ = reassocˡ ∘′ ∘-resp-≈ʳ

  ∘ʳ-resp-≈ʳ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : D ⇒ A}
             -> i ≈ g ∘ f -> i ∘ h ≈ g ∘ f ∘ h
  ∘ʳ-resp-≈ʳ = reassocʳ ∘′ ∘-resp-≈ʳ

  ∘²-resp-≈ʳ : ∀ {A B₁ B₂ C D} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
                 {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {h : D ⇒ A}
             -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> g₁ ∘ f₁ ∘ h ≈ g₂ ∘ f₂ ∘ h
  ∘²-resp-≈ʳ = reassoc² ∘′ ∘-resp-≈ʳ

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

-- Too ugly. Search for a better abstraction.
module _ {α β γ} (C : Category α β γ) where
  module First  where
    open Category C renaming (Obj to Obj₁; _⇒_ to _⇒₁_; id to id₁; _∘_ to _∘₁_;
                              idˡ to idˡ₁; idʳ to idʳ₁; assoc to assoc₁; ∘-resp-≈ to ∘-resp-≈₁;
                              _≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public
    open Heterogeneous C renaming (_≋_ to _≋₁_; hetero to hetero₁; ∘-resp-≋ to ∘-resp-≋₁;
                                   module Tools to HTools₁) public

  module Second where
    open Category C renaming (Obj to Obj₂; _⇒_ to _⇒₂_; id to id₂; _∘_ to _∘₂_;
                              idˡ to idˡ₂; idʳ to idʳ₂; assoc to assoc₂; ∘-resp-≈ to ∘-resp-≈₂;
                              _≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public
    open Heterogeneous C renaming (_≋_ to _≋₂_; hetero to hetero₂; ∘-resp-≋ to ∘-resp-≋₂;
                                   module Tools to HTools₂) public

  module Third  where
    open Category C renaming (Obj to Obj₃; _⇒_ to _⇒₃_; id to id₃; _∘_ to _∘₃_;
                              idˡ to idˡ₃; idʳ to idʳ₃; assoc to assoc₃; ∘-resp-≈ to ∘-resp-≈₃;
                              _≈_ to _≈₃_; refl to refl₃; sym to sym₃; trans to trans₃) public
    open Heterogeneous C renaming (_≋_ to _≋₃_; hetero to hetero₃; ∘-resp-≋ to ∘-resp-≋₃;
                                   module Tools to HTools₃) public

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
          { refl  = refl
          ; sym   = sym
          ; trans = trans
          }
      }
  ; id       = id
  ; _∘_      = flip _∘_
  ; idˡ      = idʳ
  ; idʳ      = idˡ
  ; assoc    = sym assoc
  ; ∘-resp-≈ = flip ∘-resp-≈
  } where open Category C
