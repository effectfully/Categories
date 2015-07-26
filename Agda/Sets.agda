module Categories.Agda.Sets where

open import Relation.Binary.PropositionalEquality

open import Categories.Category

Sets : ∀ {α} -> Category (suc α) α α
Sets {α} = record
  { Obj      = Set α
  ; _⇒_      = λ A B -> A -> B
  ; setoid   = record
      { _≈_                  = λ f g -> ∀ x -> f x ≡ g x
      ; isIndexedEquivalence = record
          { refl  = λ     x -> refl
          ; sym   = λ p   x -> sym   (p x)
          ; trans = λ p q x -> trans (p x) (q x)
          }
      }
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
