module Categories.Categories.Agda where

open import Function renaming (const to _ᵏ_)
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Categories.Category

Agda : ∀ {α} -> Category (suc α) α α
Agda {α} = record
  { Obj      = Set α
  ; _⇒_      = λ A B -> A -> B
  ; setoid   = →-ISetoid₂
  ; id       = id→
  ; _∘_      = _∘′_
  ; idˡ      = λ _ -> refl
  ; idʳ      = λ _ -> refl
  ; assoc    = λ _ -> refl
  ; ∘-resp-≈ = ∘′-resp-≡
  } where
      ∘′-resp-≡ : ∀ {α} {A B C : Set α} {g₁ g₂ : B -> C} {f₁ f₂ : A -> B}
                -> (∀ y -> g₁ y ≡ g₂ y) -> (∀ x -> f₁ x ≡ f₂ x) -> ∀ x -> g₁ (f₁ x) ≡ g₂ (f₂ x)
      ∘′-resp-≡ q p x rewrite p x = q _

,′-inj : ∀ {α β} {A : Set α} {B : Set β} {x x' : A} {y y' : B}
       -> (x , y) ≡ (x' , y') -> x ≡ x' × y ≡ y'
,′-inj refl = refl , refl

module _ {α} where
  open import Categories.Universal.Limit.Product   (Agda {α})
  open import Categories.Universal.Limit.Equalizer (Agda {α})

  binaryProducts : BinaryProducts
  binaryProducts {A} {B} = record
    { Ob        = A × B
    ; π₁        = proj₁
    ; π₂        = proj₂
    ; _↑_       = λ f g x -> f x , g x
    ; ↑-inj     = λ p -> proj₁ ∘ ,′-inj ∘ p , proj₂ ∘ ,′-inj ∘ p
    ; universal = λ p q x -> cong₂ _,_ (sym (p x)) (sym (q x))
    }

  equalizers : Equalizers
  equalizers {_} {_} {f} {g} = record
    { Ob        = ∃ λ x -> f x ≡ g x
    ; ι         = proj₁
    -- Oops, weak definition of equalizers. Coequalizers, Pullbacks, Pushouts. Tomorrow.
    ; ↙_        = λ p x -> p x , {!!}
    ; comm      = {!!}
    ; ↙-inj     = {!!}
    ; universal = {!!}
    }
