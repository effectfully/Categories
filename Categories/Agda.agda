module Categories.Categories.Agda where

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Categories.Utilities.Product
open import Categories.Category.Base

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

module _ {α} where
  open import Categories.Universal.Limit.Product   (Agda {α})
  open import Categories.Universal.Limit.Equalizer (Agda {α})
  open import Categories.Universal.Limit.Pullback  (Agda {α})
  open import Categories.Universal.Limit.Relations (Agda {α})

  binaryProducts : BinaryProducts
  binaryProducts {A} {B} = record
    { Ob        = A × B
    ; π¹        = proj₁
    ; π²        = proj₂
    ; _↑_       = <_,_>
    ; ↑-inj     = λ p -> proj₁ ∘ ,′-inj ∘ p , proj₂ ∘ ,′-inj ∘ p
    ; universal = λ p q x -> cong₂ _,_ (sym (p x)) (sym (q x))
    }

  equalizers : Equalizers
  equalizers {f = f} {g = g} = record
    { Ob        = ∃ᵢ λ x -> f x ≡ g x
    ; ι         = iproj₁
    ; ↙_⟨_⟩     = λ p r x -> p x ,ᵢ r x
    ; comm      = iproj₂
    ; ↙-inj     = λ p x -> ,ᵢ-inj₁ (p x)
    ; universal = λ r x -> ∃ᵢ-η (r x)
    }

  pullbacks : Pullbacks
  pullbacks = Product&Equalizer->Pullback binaryProducts equalizers 
