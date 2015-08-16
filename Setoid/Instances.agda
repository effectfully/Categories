module Categories.Setoid.Instances where

open import Data.Unit.Base

open import Categories.Utilities.Prelude
open import Categories.Utilities.Product
open import Categories.Setoid.Equivalence
open import Categories.Setoid.Setoid
open import Categories.Setoid.Function
open import Categories.Setoid.EqReasoning

infix 3 _↣ₕ_ _↣_

⊤-ISetoid : ∀ {ι α} {I : Set ι} {A : I -> Set α} -> ISetoid A zero
⊤-ISetoid = record { _≈_ = λ _ _ -> ⊤ }

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
            -> ISetoid₂ (λ (Aˢ Bˢ : [ Setoid A γ ∣ A ∈ Set α ]) -> reveal Aˢ ─> reveal Bˢ) (α ⊔ γ)
─>-ISetoid₂ = record
      { _≈_            = _≗_
      ; isIEquivalence = record
          { refl  = λ {_ f} r -> Π.f-resp-≈ f r
          ; sym   = λ{ {hide Aˢ , hide Bˢ} p   r -> Setoid.sym   Bˢ (p (Setoid.sym  Aˢ r))     }
          ; trans = λ{ {hide Aˢ , hide Bˢ} p q r -> Setoid.trans Bˢ (p (Setoid.refl Aˢ)) (q r) }
          }
      }

module HIEquality where
  private open module  Heq {ι α} {I : Set ι} (A : I -> Set α) =
                         Hetero (≡-ISetoid {A = A}) using (_≋_)
  heq = _≋_
  syntax heq A x y = x [ A ]≅ y
  private open module IHeq {ι α} {I : Set ι} {A : I -> Set α} =
                         Hetero (≡-ISetoid {A = A}) hiding (_≋_) public

module Just-HEquality {α} = Hetero (≡-ISetoid {α = α} {A = id′}) renaming (_≋_ to _≅_)

module HEquality where
  open Just-HEquality hiding (hrefl) public

  pattern hrefl = hetero prefl

  hcong : ∀ {α β} {A : Set α} {B : A -> Set β} {x y} -> (f : ∀ x -> B x) -> x ≅ y -> f x ≅ f y
  hcong f hrefl = hrefl

  hsubst : ∀ {α β} {A : Set α} {x y} -> (B : A -> Set β) -> x ≅ y -> B x -> B y
  hsubst B hrefl = id′

_↣ₕ_ : ∀ {α β} -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
A ↣ₕ B = HInjection (≡-Setoid {A = A}) (≡-HSetoid {A = B})
  where open HIEquality renaming (hsetoid to ≡-HSetoid)

_↣_ : ∀ {α β} -> Set α -> Set β -> Set (α ⊔ β)
A ↣ B = A ↣ₕ λ _ -> B

module ≡-Reasoning {α} {A : Set α} = EqReasoning (≡-Setoid {A = A})

module ≅-Reasoning {α} where
  open Just-HEquality {α}; open HEqReasoning hsetoid public

private
  module Test where
    open import Function
    open import Data.Nat
    open import Data.Nat.Properties.Simple
    open import Data.Fin hiding (_+_)
    
    open HEquality
    open ≅-Reasoning

    test : ∀ n m -> (Fin (ℕ.suc n + m) ∋ Fin.zero) ≅ (Fin (ℕ.suc m + n) ∋ Fin.zero)
    test n m =
      begin
        Fin.zero →⟨ hcong (λ n -> Fin (ℕ.suc n) ∋ Fin.zero) (hetero (+-comm n m)) ⟩
        Fin.zero
      ∎
