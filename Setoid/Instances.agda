module Categories.Setoid.Instances where

open import Data.Unit.Base

open import Categories.Utilities.Prelude
open import Categories.Setoid.Equivalence
open import Categories.Setoid.Setoid
open import Categories.Setoid.Function
open import Categories.Setoid.EqReasoning

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
      { refl  = prefl
      ; sym   = psym
      ; trans = ptrans
      }
  }

≡-Setoid : ∀ {α} {A : Set α} -> Setoid A α
≡-Setoid = inst tt where open ISetoid ≡-ISetoid

→-ISetoid₂ : ∀ {α} -> ISetoid₂ (λ (A B : Set α) -> A -> B) α
→-ISetoid₂ = record
      { _≈_            = _≗ₚ_
      ; isIEquivalence = record
          { refl  = λ     x -> prefl
          ; sym   = λ p   x -> psym   (p x)
          ; trans = λ p q x -> ptrans (p x) (q x)
          }
      }

─>-ISetoid₂ : ∀ {α γ}
            -> ISetoid₂ (λ (Aˢ Bˢ : Setoid A γ , A ∈ Set α) -> struct Aˢ ─> struct Bˢ) (α ⊔ γ)
─>-ISetoid₂ = record
      { _≈_            = _≗_
      ; isIEquivalence = record
          { refl  = λ {_ f} r -> ⟨⟩-resp-≈ f r
          ; sym   = λ{ {Aˢ , Bˢ} p   r ->
              Setoid.sym   (struct Bˢ) (p (Setoid.sym  (struct Aˢ) r))     }
          ; trans = λ{ {Aˢ , Bˢ} p q r ->
              Setoid.trans (struct Bˢ) (p (Setoid.refl (struct Aˢ))) (q r) }
          }
      } where open Π

module HIEquality where
  private open module  Heq {ι α} {I : Set ι} (A : I -> Set α) =
                         Hetero (≡-ISetoid {A = A}) using (_≋_)
  heq = _≋_
  syntax heq A x y = x [ A ]≅ y
  private open module IHeq {ι α} {I : Set ι} {A : I -> Set α} =
                         Hetero (≡-ISetoid {A = A}) hiding (_≋_) public
                         
module HEquality {α} = Hetero (≡-ISetoid {α = α} {A = id′}) renaming (_≋_ to _≅_)

module ≡-Reasoning {α} {A : Set α} = EqReasoning (≡-Setoid {A = A})

-- Doesn't work.
module ≅-Reasoning {α} where
  open HEquality {α}; open HEqReasoning hsetoid public

private
  module Test where
    open import Function
    open import Data.Nat
    open import Data.Nat.Properties.Simple
    open import Data.Fin hiding (_+_)
    open HEquality

    test : ∀ n m -> (Fin (ℕ.suc n + m) ∋ Fin.zero) ≅ (Fin (ℕ.suc m + n) ∋ Fin.zero)
    test n m rewrite +-comm n m = hrefl
