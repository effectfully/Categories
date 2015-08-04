module Categories.Utilities.Prelude where

open import Level public
open import Function using (flip; _$_; const; case_of_) renaming (id to id′; _∘_ to _∘′_) public
open import Relation.Binary.PropositionalEquality
  renaming (refl to prefl; sym to psym; trans to ptrans; _≗_ to _≗ₚ_)
  using (_≡_; subst; subst₂; cong; cong₂) public
open import Data.Product renaming (_×_ to _×ₚ_) public

infixl 10 _%
_% = _∘′_

record Tag {α β} {A : Set α} (B : (x : A) -> Set β) (x : A) : Set β where
  constructor tag
  field detag : B x
  tagOf = x
open Tag public

Tag₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} -> (∀ x -> B x -> Set γ) -> ∀ x -> B x -> Set _
Tag₂ C x y = Tag (uncurry C) (x , y)

Tag₃ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
     -> (∀ x -> (y : B x) -> C y -> Set δ) -> ∀ x -> (y : B x) -> C y -> Set _
Tag₃ D x y z = Tag (uncurry (uncurry ∘′ D)) (x , y , z)

tagWith : ∀ {α β} {A : Set α} {B : (x : A) -> Set β} -> (x : A) -> B x -> Tag B x
tagWith _ = tag

record Struct {α β} (A : Set α) (B : A -> Set β) : Set (α ⊔ β) where
  field
    carrier : A
    struct  : B carrier
open Struct public

syntax Struct A (λ x -> B) = B , x ∈ A
