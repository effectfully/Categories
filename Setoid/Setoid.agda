module Categories.Setoid.Setoid where

open import Data.Unit.Base

open import Categories.Utilities.Prelude
open import Categories.Setoid.Equivalence

module Setoid-Module where
  record Setoid {α} (A : Set α) β : Set (α ⊔ suc β) where
    infix 4 _≈_
  
    field
      _≈_           : A -> A -> Set β
      isEquivalence : IsEquivalence _≈_
open Setoid-Module renaming (module Setoid to Just-Setoid) public

module Setoid {α β} {A : Set α} (setoid : Setoid A β) where
  open Just-Setoid setoid public; open IsEquivalence isEquivalence public

module ISetoid-Module where
  record ISetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
    infix 4 _≈_
  
    field
      _≈_            : ∀ {i} -> A i -> A i -> Set β
      isIEquivalence : IsIEquivalence A _≈_

    inst : ∀ i -> Setoid (A i) β
    inst i = record
      { _≈_           = _≈_
      ; isEquivalence = Eq.inst i
      } where module Eq = IsIEquivalence isIEquivalence
open ISetoid-Module renaming (module ISetoid to Just-ISetoid) public

module ISetoid {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open Just-ISetoid isetoid public; open IsIEquivalence isIEquivalence hiding (inst) public

module HSetoid-Module where
  record HSetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
    infix 4 _≈_
  
    field
      _≈_            : ∀ {i j} -> A i -> A j -> Set β
      isHEquivalence : IsHEquivalence A _≈_

    hinst : ∀ i -> Setoid (A i) β
    hinst i = record
      { _≈_           = _≈_
      ; isEquivalence = Eq.hinst i
      } where module Eq = IsHEquivalence isHEquivalence
open HSetoid-Module renaming (module HSetoid to Just-HSetoid) public

module HSetoid {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open Just-HSetoid hsetoid public; open IsHEquivalence isHEquivalence hiding (hinst) public

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

  -- We can define `hsetoid' in terms of `isetoid', but this breaks some definitional equalities.
  hsetoid : ∀ {ι} {I : Set ι} -> HSetoid (λ (_ : I) -> A) β
  hsetoid = record
    { _≈_            = _≈_
    ; isHEquivalence = record
        { hrefl  = refl
        ; hsym   = sym
        ; htrans = trans
        }
    }
    
module Just-Hetero {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
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
        { hrefl  = hetero refl
        ; hsym   = hlift₁ (hetero ∘′ sym)
        ; htrans = hlift₂ (hetero % ∘′ trans)
        }
    }

module Hetero {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open Just-Hetero isetoid public; open HSetoid hsetoid hiding (_≈_) public

module _ {α β} {A : Set α} (setoid : Setoid A β) where
  module Setoid₁ where
    open Just-Setoid setoid renaming (_≈_ to _≈₁_) public
    open IsEquivalence₁ isEquivalence public
    
  module Setoid₂ where
    open Just-Setoid setoid renaming (_≈_ to _≈₂_) public
    open IsEquivalence₂ isEquivalence public
    
  module Setoid₃ where
    open Just-Setoid setoid renaming (_≈_ to _≈₃_) public
    open IsEquivalence₃ isEquivalence public

module _ {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  module ISetoid₁ where
    open Just-ISetoid isetoid renaming (_≈_ to _≈₁_) public
    open IsIEquivalence₁ isIEquivalence hiding (inst) public
    
  module ISetoid₂ where
    open Just-ISetoid isetoid renaming (_≈_ to _≈₂_) public
    open IsIEquivalence₂ isIEquivalence hiding (inst) public
    
  module ISetoid₃ where
    open Just-ISetoid isetoid renaming (_≈_ to _≈₃_) public
    open IsIEquivalence₃ isIEquivalence hiding (inst) public

module _ {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  module HSetoid₁ where
    open Just-HSetoid hsetoid renaming (_≈_ to _≈₁_) public
    open IsHEquivalence₁ isHEquivalence hiding (hinst) public
    
  module HSetoid₂ where
    open Just-HSetoid hsetoid renaming (_≈_ to _≈₂_) public
    open IsHEquivalence₂ isHEquivalence hiding (hinst) public
    
  module HSetoid₃ where
    open Just-HSetoid hsetoid renaming (_≈_ to _≈₃_) public
    open IsHEquivalence₃ isHEquivalence hiding (hinst) public
