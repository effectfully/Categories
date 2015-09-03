module Categories.Setoid.Setoid where

open import Categories.Utilities.Prelude
open import Categories.Utilities.Product
open import Categories.Setoid.Equivalence

module Setoid-Module where
  record Setoid {α} (A : Set α) β : Set (α ⊔ suc β) where
    infix 4 _≈_
  
    field
      _≈_           : A -> A -> Set β
      isEquivalence : IsEquivalence _≈_
open Setoid-Module renaming (module Setoid to Just-Setoid) public

module Setoid {α β} {A : Set α} (setoid : Setoid A β) where
  open Just-Setoid setoid          public
  open IsEquivalence isEquivalence public
  open EqTools                     public

module ISetoid-Module where
  record ISetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
    infix 4 _≈_
  
    field
      _≈_            : ∀ {i} -> A i -> A i -> Set β
      isIEquivalence : IsIEquivalence A _≈_
open ISetoid-Module renaming (module ISetoid to Just-ISetoid) public

module ISetoid {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open Just-ISetoid isetoid          public
  open IsIEquivalence isIEquivalence public
  open EqTools                       public

module HSetoid-Module where
  record HSetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
    infix 4 _≈_
  
    field
      _≈_            : ∀ {i j} -> A i -> A j -> Set β
      isHEquivalence : IsHEquivalence A _≈_
open HSetoid-Module renaming (module HSetoid to Just-HSetoid) public

module HSetoid {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open Just-HSetoid hsetoid          public
  open IsHEquivalence isHEquivalence public
  open HEqTools                      public

instⁱˢ : ∀ {ι α β} {I : Set ι} {A : I -> Set α} -> ∀ i -> ISetoid A β -> Setoid (A i) β
instⁱˢ i isetoid = record { isEquivalence = instⁱᵉ i isIEquivalence }
  where open ISetoid isetoid

instʰˢ : ∀ {ι α β} {I : Set ι} {A : I -> Set α} -> ∀ i -> HSetoid A β -> Setoid (A i) β
instʰˢ i hsetoid = record { isEquivalence = instʰᵉ i isHEquivalence }
  where open HSetoid hsetoid

ISetoid₂ : ∀ {ι₁ ι₂ α} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂} (A : ∀ i₁ -> I₂ i₁ -> Set α) β
         -> Set (ι₁ ⊔ ι₂ ⊔ α ⊔ suc β)
ISetoid₂ A = ISetoid (uncurry A)

HSetoid₂ : ∀ {ι₁ ι₂ α} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂} (A : ∀ i₁ -> I₂ i₁ -> Set α) β
         -> Set (ι₁ ⊔ ι₂ ⊔ α ⊔ suc β)
HSetoid₂ A = HSetoid (uncurry A)

comap∀ⁱˢₑ : ∀ {ι₁ ι₂ α₁ α₂ β γ} {I₁ : Set ι₁} {I₂ : Set ι₂}
              {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂}
              {B : I₁ -> Set β} {k : ∀ {i₁} -> B i₁ -> I₂}
          -> (∀ {i₁} -> A₁ i₁ -> (z : B i₁) -> A₂ (k z))
          -> ISetoid A₂ γ
          -> ISetoid A₁ (β ⊔ γ)
comap∀ⁱˢₑ f isetoid = record { isIEquivalence = comap∀ⁱᵉₑ f isIEquivalence }
  where open ISetoid isetoid

comap∀ⁱˢ : ∀ {ι₁ ι₂ α₁ α₂ β γ} {I₁ : Set ι₁} {I₂ : Set ι₂}
             {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂}
             {B : I₁ -> Set β} {k : ∀ {i₁} -> B i₁ -> I₂}
         -> (∀ {i₁} -> A₁ i₁ -> (z : B i₁) -> A₂ (k z))
         -> ISetoid A₂ γ
         -> ISetoid A₁ (β ⊔ γ)
comap∀ⁱˢ f isetoid = record { isIEquivalence = comap∀ⁱᵉ f isIEquivalence }
  where open ISetoid isetoid

-- We could write (comapⁱˢ f = comap∀ⁱˢ λ{ x tt -> f x }),
-- but then some functions would require η-expansion.
comapⁱˢ : ∀ {ι₁ ι₂ α₁ α₂ β} {I₁ : Set ι₁} {I₂ : Set ι₂}
            {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂} {k : I₁ -> I₂}
        -> (∀ {i₁} -> A₁ i₁ -> A₂ (k i₁)) -> ISetoid A₂ β -> ISetoid A₁ β
comapⁱˢ f isetoid = record { isIEquivalence = comapⁱᵉ f isIEquivalence }
  where open ISetoid isetoid

comapⁱˢ₁ : ∀ {ι α₁ α₂ β} {I : Set ι} {A₁ : I -> Set α₁} {A₂ : I -> Set α₂} 
         -> (∀ {i₁} -> A₁ i₁ -> A₂ i₁) -> ISetoid A₂ β -> ISetoid A₁ β
comapⁱˢ₁ = comapⁱˢ

coerceⁱˢ : ∀ {ι₁ ι₂ α β} {I₁ : Set ι₁} {I₂ : Set ι₂} {A : I₂ -> Set α} {k : I₁ -> I₂}
         -> ISetoid A β -> ISetoid (A ∘′ k) β
coerceⁱˢ = comapⁱˢ id′

reduceⁱˢ : ∀ {ι α β} {I : Set ι} {A : I -> I -> Set α}
         -> ISetoid₂ A β -> ISetoid (λ i -> A i i) β
reduceⁱˢ = coerceⁱˢ

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
    open Just-Setoid setoid renaming (_≈_ to _≈₁_; isEquivalence to isEquivalence₁) public
    open IsEquivalence₁ isEquivalence₁ public
    
  module Setoid₂ where
    open Just-Setoid setoid renaming (_≈_ to _≈₂_; isEquivalence to isEquivalence₂) public
    open IsEquivalence₂ isEquivalence₂ public
    
  module Setoid₃ where
    open Just-Setoid setoid renaming (_≈_ to _≈₃_; isEquivalence to isEquivalence₃) public
    open IsEquivalence₃ isEquivalence₃ public

module _ {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  module ISetoid₁ where
    open Just-ISetoid isetoid renaming (_≈_ to _≈₁_; isIEquivalence to isIEquivalence₁) public
    open IsIEquivalence₁ isIEquivalence₁ public
    
  module ISetoid₂ where
    open Just-ISetoid isetoid renaming (_≈_ to _≈₂_; isIEquivalence to isIEquivalence₂) public
    open IsIEquivalence₂ isIEquivalence₂ public
    
  module ISetoid₃ where
    open Just-ISetoid isetoid renaming (_≈_ to _≈₃_; isIEquivalence to isIEquivalence₃) public
    open IsIEquivalence₃ isIEquivalence₃ public

module _ {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  module HSetoid₁ where
    open Just-HSetoid hsetoid renaming (_≈_ to _≈₁_; isHEquivalence to isHEquivalence₁) public
    open IsHEquivalence₁ isHEquivalence₁ public
    
  module HSetoid₂ where
    open Just-HSetoid hsetoid renaming (_≈_ to _≈₂_; isHEquivalence to isHEquivalence₂) public
    open IsHEquivalence₂ isHEquivalence₂ public
    
  module HSetoid₃ where
    open Just-HSetoid hsetoid renaming (_≈_ to _≈₃_; isHEquivalence to isHEquivalence₃) public
    open IsHEquivalence₃ isHEquivalence₃ public

_×ⁱˢ_ : ∀ {ι₁ ι₂ ι₃ α₁ α₂ β₁ β₂} {I₁ : Set ι₁} {I₂ : Set ι₂} {I₃ : Set ι₃}
          {k₁ : I₃ -> I₁} {k₂ : I₃ -> I₂} {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂}
      -> ISetoid A₁ β₁ -> ISetoid A₂ β₂ -> ISetoid (λ i₃ -> A₁ (k₁ i₃) ×ₚ A₂ (k₂ i₃)) (β₁ ⊔ β₂)
Aˢ₁ ×ⁱˢ Aˢ₂ = record { isIEquivalence = isIEquivalence₁ ×ⁱᵉ isIEquivalence₂ }
  where open ISetoid₁ Aˢ₁; open ISetoid₂ Aˢ₂

_×ⁱˢₖ₂_ : ∀ {ι₁ ι₂ α₁ α₂ β₁ β₂} {I₁ : Set ι₁} {I₂ : Set ι₂}
            {k : I₂ -> I₁} {A₁ : I₁ -> Set α₁} {A₂ : I₁ -> Set α₂}
        -> ISetoid A₁ β₁ -> ISetoid A₂ β₂ -> ISetoid₂ (λ i₁ i₂ -> A₁ (k i₁) ×ₚ A₂ (k i₂)) (β₁ ⊔ β₂)
_×ⁱˢₖ₂_ = _×ⁱˢ_

_×ⁱˢₖ₁_ : ∀ {ι₁ ι₂ α₁ α₂ β₁ β₂} {I₁ : Set ι₁} {I₂ : Set ι₂}
            {k : I₂ -> I₁} {A₁ : I₁ -> Set α₁} {A₂ : I₁ -> Set α₂}
        -> ISetoid A₁ β₁ -> ISetoid A₂ β₂ -> ISetoid (λ i -> A₁ (k i) ×ₚ A₂ (k i)) (β₁ ⊔ β₂)
_×ⁱˢₖ₁_  = reduceⁱˢ % ∘′ _×ⁱˢₖ₂_

_×ⁱˢ₂_ : ∀ {ι α₁ α₂ β₁ β₂} {I : Set ι} {A₁ : I -> Set α₁} {A₂ : I -> Set α₂}
       -> ISetoid A₁ β₁ -> ISetoid A₂ β₂ -> ISetoid₂ (λ i₁ i₂ -> A₁ i₁ ×ₚ A₂ i₂) (β₁ ⊔ β₂)
_×ⁱˢ₂_ = _×ⁱˢₖ₂_

_×ⁱˢ₁_ : ∀ {ι α₁ α₂ β₁ β₂} {I : Set ι} {A₁ : I -> Set α₁} {A₂ : I -> Set α₂}
       -> ISetoid A₁ β₁ -> ISetoid A₂ β₂ -> ISetoid (λ i -> A₁ i ×ₚ A₂ i) (β₁ ⊔ β₂)
_×ⁱˢ₁_  = _×ⁱˢₖ₁_

_×ˢ_ : ∀ {α₁ α₂ β₁ β₂} {A₁ : Set α₁} {A₂ : Set α₂}
     -> Setoid A₁ β₁ -> Setoid A₂ β₂ -> Setoid (A₁ ×ₚ A₂) (β₁ ⊔ β₂)
Aˢ₁ ×ˢ Aˢ₂ = instⁱˢ tt (Aˢᵢ₁ ×ⁱˢ₁ Aˢᵢ₂)
  where open Indexed Aˢ₁ renaming (isetoid to Aˢᵢ₁)
        open Indexed Aˢ₂ renaming (isetoid to Aˢᵢ₂)
