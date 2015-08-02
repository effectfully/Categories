module Categories.Utilities.Prelude where

open import Level public
open import Function using (flip; _$_; case_of_) renaming (id to id′; _∘_ to _∘′_) public
open import Relation.Binary.PropositionalEquality
  renaming (refl to prefl; sym to psym; trans to ptrans; _≗_ to _≗ₚ_)
  using (_≡_; subst; subst₂; cong; cong₂) public
open import Data.Product renaming (_×_ to _×ₚ_) public

infixl 10 _%
_% = _∘′_

record Struct {α β} (A : Set α) (B : A -> Set β) : Set (α ⊔ β) where
  field
    {carrier} : A
    struct    : B carrier
open Struct public

syntax Struct A (λ x -> B) = B , x ∈ A
