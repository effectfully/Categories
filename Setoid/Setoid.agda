module Categories.Setoid.Setoid where

open import Level
open import Function
open import Data.Product

open import Categories.Setoid.Equivalence

infixl 10 _%
_% = _∘_

record Setoid {α} (A : Set α) β : Set (α ⊔ suc β) where
  infix 4 _≈_
  
  field
    _≈_           : A -> A -> Set β
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

record ISetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
  infix 4 _≈_
  
  field
    _≈_            : ∀ {i} -> A i -> A i -> Set β
    isIEquivalence : IsIEquivalence A _≈_

  private open module Eq = IsIEquivalence isIEquivalence hiding (inst) public

  inst : ∀ i -> Setoid (A i) β
  inst i = record
    { _≈_           = _≈_
    ; isEquivalence = Eq.inst i
    }

record HSetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
  infix 4 _≈_
  
  field
    _≈_            : ∀ {i j} -> A i -> A j -> Set β
    isHEquivalence : IsHEquivalence A _≈_

  private open module Eq = IsHEquivalence isHEquivalence hiding (inst) public

  inst : ∀ i -> Setoid (A i) β
  inst i = record
    { _≈_           = _≈_
    ; isEquivalence = Eq.inst i
    }

ISetoid₂ : ∀ {ι₁ ι₂ α} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂} (A : ∀ i₁ -> I₂ i₁ -> Set α) β
         -> Set (ι₁ ⊔ ι₂ ⊔ α ⊔ suc β)
ISetoid₂ A = ISetoid (uncurry A)

module Indexed {α β} {A : Set α} (setoid : Setoid A β) where
  open Setoid setoid

  isetoid : ∀ {ι} {I : Set ι} -> ISetoid (λ (_ : I) -> A) β
  isetoid = record
    { _≈_            = _≈_
    ; isIEquivalence = record
        { refl  = refl
        ; sym   = sym
        ; trans = trans
        }
    }

module Hetero {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open ISetoid isetoid

  infix 4 _≋_

  data _≋_ {i} (x : A i) : ∀ {j} -> A j -> Set β where
    hetero : {y : A i} -> x ≈ y -> x ≋ y

  homo : ∀ {i} {x y : A i} -> x ≋ y -> x ≈ y
  homo (hetero x≈y) = x≈y

  hlift₁ : ∀ {γ i j} {C : ∀ {i j} -> A i -> A j -> Set γ} {x : A i} {y : A j}
         -> (∀ {i} {x y : A i} -> x ≈ y -> C x y) -> x ≋ y -> C x y
  hlift₁ f (hetero x≈y) = f x≈y

  -- Here we "connect" `x₂' and `y₁'. We can "connect" any `xᵢ' with any `yⱼ',
  -- so there are four ways to define this function. Hence it's rather ad hoc.
  hlift₂ : ∀ {γ i₁ i₂ j₁ j₂} {C : ∀ {i₁ j₂} -> A i₁ -> A j₂ -> Set γ}
             {x₁ : A i₁} {x₂ : A i₂} {y₁ : A j₁} {y₂ : A j₂}
         -> ({x₁' : A i₂} {y₂' : A j₁} -> x₁' ≈ x₂ -> y₁ ≈ y₂' -> C x₁' y₂')
         -> x₁ ≋ x₂ -> y₁ ≋ y₂ -> C x₁ y₂
  hlift₂ f (hetero x₁≈x₂) (hetero y₁≈y₂) = f x₁≈x₂ y₁≈y₂

  hsetoid : HSetoid A β
  hsetoid = record
    { _≈_            = λ x y -> x ≋ y
    ; isHEquivalence = record
        { refl  = hetero refl
        ; sym   = hlift₁ (hetero ∘ sym)
        ; trans = hlift₂ (hetero % ∘ trans)
        }
    }

  open HSetoid hsetoid public hiding (_≈_)

module Setoid₁ {α β} {A : Set α} (setoid : Setoid A β) where
  open Setoid setoid renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public

module Setoid₂ {α β} {A : Set α} (setoid : Setoid A β) where
  open Setoid setoid renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public

module ISetoid₁ {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open ISetoid isetoid renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public

module ISetoid₂ {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open ISetoid isetoid renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public

module HSetoid₁ {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open HSetoid hsetoid renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public

module HSetoid₂ {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open HSetoid hsetoid renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public
