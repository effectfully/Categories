module Categories.Setoid.Instances where

open import Level
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base

open import Categories.Setoid.Equivalence
open import Categories.Setoid.Setoid

⊤-ISetoid : ∀ {ι α} {I : Set ι} {A : I -> Set α} -> ISetoid A zero
⊤-ISetoid = record
  { _≈_            = λ _ _ -> ⊤
  ; isIEquivalence = record
      { refl  = _
      ; sym   = _
      ; trans = _
       }
  }

≡-ISetoid : ∀ {ι α} {I : Set ι} {A : I -> Set α} -> ISetoid A α
≡-ISetoid = record
  { _≈_            = _≡_
  ; isIEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
       }
  }

≡-Setoid : ∀ {α} {A : Set α} -> Setoid A α
≡-Setoid = ISetoid.inst ≡-ISetoid tt

→-ISetoid₂ : ∀ {α} -> ISetoid₂ (λ (A B : Set α) -> A -> B) α
→-ISetoid₂ = record
      { _≈_            = λ f g -> ∀ x -> f x ≡ g x
      ; isIEquivalence = record
          { refl  = λ     x -> refl
          ; sym   = λ p   x -> sym   (p x)
          ; trans = λ p q x -> trans (p x) (q x)
          }
      }

module HIEquality where
  open module  Heq {ι α} {I : Set ι} (A : I -> Set α) = Hetero (≡-ISetoid {A = A}) using (_≋_)
  heq = _≋_
  syntax heq A x y = x [ A ]≅ y
  open module IHeq {ι α} {I : Set ι} {A : I -> Set α} = Hetero (≡-ISetoid {A = A}) public

module HEquality {α} = Hetero (≡-ISetoid {α = α} {A = id}) renaming (_≋_ to _≅_)

module Test where
  open import Data.Nat
  open import Data.Nat.Properties.Simple
  open import Data.Fin hiding (_+_)
  open HEquality renaming (refl to hrefl)

  test : ∀ n m -> (Fin (ℕ.suc n + m) ∋ Fin.zero) ≅ (Fin (ℕ.suc m + n) ∋ Fin.zero)
  test n m rewrite +-comm n m = hrefl
