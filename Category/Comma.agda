open import Categories.Category.Category
open import Categories.Functor.Functor

module Categories.Category.Comma
  {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
  {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
  (F₁ : Functor C₁ C₃) (F₂ : Functor C₂ C₃) where

open import Data.Product

open Category₁ C₁; open Category₂ C₂; open Category₃ C₃
open Functor₁ F₁; open Functor₂ F₂

Comma : Category (α₁ ⊔ α₂ ⊔ β₃) (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₃) (γ₁ ⊔ γ₂)
Comma = record
  { Obj      = Obj
  ; _⇒_      = _⇒_
  ; setoid   = record
      { _≈_            = _≈_
      ; isIEquivalence = record
          { refl  = refl₁ , refl₂
          ; sym   = map sym₁ sym₂
          ; trans = zip trans₁ trans₂
          }
      }
  ; id       = id
  ; _∘_      = _∘_
  ; idˡ      = idˡ₁ , idˡ₂
  ; idʳ      = idʳ₁ , idʳ₂
  ; assoc    = assoc₁ , assoc₂
  ; ∘-resp-≈ = zip ∘-resp-≈₁ ∘-resp-≈₂
  } where
      record Obj : Set (α₁ ⊔ α₂ ⊔ β₃) where
        field
          A : Obj₁
          B : Obj₂
          h : F·₁ A ⇒₃ F·₂ B 

      module _ (A : Obj) where
        module Obj₁ where open Obj A renaming (A to A₁; B to B₁; h to h₁) public
        module Obj₂ where open Obj A renaming (A to A₂; B to B₂; h to h₂) public

      record _⇒_ (A B : Obj) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₃) where
        open Obj₁ A; open Obj₂ B

        field
          f    : A₁ ⇒₁ A₂
          g    : B₁ ⇒₂ B₂
          comm : h₂ ∘₃ F⇒₁ f ≈₃ F⇒₂ g ∘₃ h₁

      module _ {A B} (f : A ⇒ B) where
        module Arr₁ where open _⇒_ f renaming (f to f₁; g to g₁; comm to comm₁) public
        module Arr₂ where open _⇒_ f renaming (f to f₂; g to g₂; comm to comm₂) public

      _≈_ : ∀ {A B} -> A ⇒ B -> A ⇒ B -> Set (γ₁ ⊔ γ₂)
      h₁ ≈ h₂ = f₁ ≈₁ f₂ × g₁ ≈₂ g₂
        where open Arr₁ h₁; open Arr₂ h₂

      id : ∀ {A} -> A ⇒ A
      id = record
        { f    = id₁
        ; g    = id₂
        ; comm = ?
        }
      
      _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C
      h₂ ∘ h₁ = record
        { f    = f₂ ∘₁ f₁
        ; g    = g₂ ∘₂ g₁
        ; comm = {!!}
        } where open Arr₁ h₁; open Arr₂ h₂
