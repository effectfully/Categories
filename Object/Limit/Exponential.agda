open import Categories.Category

module Categories.Object.Limit.Exponential {α β γ} (ℂ : Category α β γ) where

open import Categories.Object.Limit.Product ℂ
open Category ℂ

module Exponentials ([_×_] : BinaryProducts) where
  open ProductTools [_×_]

  record Exponential B A : Set (α ⊔ β ⊔ γ) where
    field
      B^A  : Obj
      eval : B^A × A ⇒ B
      curr : ∀ {C} -> C × A ⇒ B -> C ⇒ B^A

      curr-inj  : ∀ {C} {g₁ g₂ : C × A ⇒ B} -> curr g₁ ≈ curr g₂ -> g₁ ≈ g₂
      curr-univ : ∀ {C h} {g : C × A ⇒ B} -> eval ∘ pfirst h ≈ g -> curr g ≈ h

    curr-eval : ∀ {C} {h : C ⇒ B^A} -> curr (eval ∘ pfirst h) ≈ h
    curr-eval = curr-univ refl

    eval-curr : ∀ {C} {g : C × A ⇒ B} -> eval ∘ pfirst (curr g) ≈ g
    eval-curr = curr-inj curr-eval 

    curr-resp-≈ : ∀ {C} {g₁ g₂ : C × A ⇒ B} -> g₁ ≈ g₂ -> curr g₁ ≈ curr g₂
    curr-resp-≈ p = curr-univ (left eval-curr p)

  Exponentials = ∀ B A -> Exponential B A
open Exponentials using (Exponentials) public

module ExponentialTools {[_×_] : BinaryProducts} ([_^_] : Exponentials [_×_]) where
  open Exponentials [_×_]

  open module ImplicitExponential {B} {A} = Exponential [ B ^ A ] hiding (B^A) public

  infixr 8 _^_

  _^_ : Obj -> Obj -> Obj
  B ^ A = Exponential.B^A [ B ^ A ]
