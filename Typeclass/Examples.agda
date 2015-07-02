module Categories.Typeclass.Examples where

import Function as F
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.List.Base
open import Data.List.Properties

open import Categories.Typeclass.Category
open import Categories.Typeclass.Functor

∘′-resp-≡ : ∀ {α} {A B C : Set α} {g₁ g₂ : B -> C} {f₁ f₂ : A -> B}
          -> (∀ y -> g₁ y ≡ g₂ y) -> (∀ x -> f₁ x ≡ f₂ x) -> ∀ x -> g₁ (f₁ x) ≡ g₂ (f₂ x)
∘′-resp-≡ q p x rewrite p x = q _

instance
  →-Setoid : ∀ {α} {A B : Set α} {{setoid : Setoid B}} -> Setoid (A -> B)
  →-Setoid {α} {A} {B} = record
    { _≈_           = λ f g -> ∀ x -> f x ≈ g x
    ; isEquivalence = record
      { refl  = λ f     x -> refl  (f x)
      ; sym   = λ f p   x -> sym   (f x) (p x)
      ; trans = λ f p q x -> trans (f x) (p x) (q x)
      }
    }

  ≡-Setoid : ∀ {α} {A : Set α} -> Setoid A
  ≡-Setoid = record
    { _≈_           = _≡_
    ; isEquivalence = record
      { refl  = λ _ -> P.refl
      ; sym   = λ _ -> P.sym
      ; trans = λ _ -> P.trans
      }
    }

  →-IsCategory : ∀ {α} -> IsCategory (λ (A B : Set α) -> A -> B)
  →-IsCategory = record
    { id       = F.id
    ; _∘_      = F._∘′_
    ; idˡ      = λ x -> P.refl
    ; idʳ      = λ x -> P.refl
    ; assoc    = λ x -> P.refl
    ; ∘-resp-≈ = ∘′-resp-≡
    }
    
  →-IsEndofunctor : ∀ {α} {R : Set α} -> IsEndofunctor (λ (A B : Set α) -> A -> B) (λ Q -> R -> Q)
  →-IsEndofunctor {α} {C} = record
    { F₁       = F._∘′_
    ; F-id     = λ x -> P.refl
    ; F-∘      = λ x -> P.refl
    ; F-resp-≈ = λ p f -> ext (λ x -> p (f x))
    } where postulate ext : P.Extensionality _ _

  List-IsEndofunctor : ∀ {α} -> IsEndofunctor (λ (A B : Set α) -> A -> B) List
  List-IsEndofunctor = record
    { F₁       = map
    ; F-id     = map-id
    ; F-∘      = map-compose
    ; F-resp-≈ = map-cong
    }

module Test where
  _<$>_ : ∀ {α} {F₀ : Set α -> Set α} {A B : Set α}
            {{isEndofunctor : IsEndofunctor (λ A B -> A -> B) F₀}}
        -> (A -> B) -> F₀ A -> F₀ B
  _<$>_ = F₁

  open import Data.Nat
  open import Data.Nat.Properties.Simple

  test : ∀ n m -> n + m ≡ m + n
  test  ℕ.zero   m =
    m     ≈⟨ P.sym (+-right-identity m) ⟩
    m + 0 ∎
  test (ℕ.suc n) m =
    ℕ.suc (n + m) ≈⟨ P.cong ℕ.suc (+-comm n m) ⟩
    ℕ.suc (m + n) ≈⟨ P.sym (+-suc m n) ⟩
    m + ℕ.suc n   ∎

  test-→ : (List ℕ -> ℕ) -> (ℕ -> List ℕ) -> ℕ -> ℕ
  test-→ = _<$>_

  test-List : List ℕ
  test-List = ℕ.suc <$> (1 ∷ 2 ∷ 3 ∷ [])
