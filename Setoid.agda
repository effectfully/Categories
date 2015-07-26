module Categories.Setoid where

open import Level
open import Function hiding (_⟨_⟩_)
open import Data.Product

infixr 10 _%
_% = _∘_

record IsEquivalence {α β} {A : Set α} (_≈_ : A -> A -> Set β) : Set (α ⊔ β) where
  field
    refl  : ∀ {x}     -> x ≈ x
    sym   : ∀ {x y}   -> x ≈ y -> y ≈ x
    trans : ∀ {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

  module Tools where
    infix  2 _⟨_⟩_ _⟩_⟨_
    infixl 3 _⋯_

    _⋯_ = trans

    left  : ∀ {x y z} -> x ≈ y -> z ≈ y -> x ≈ z
    left  p q = trans p (sym q)

    right : ∀ {x y z} -> x ≈ y -> x ≈ z -> y ≈ z
    right p q = trans (sym p) q

    _⟨_⟩_ : ∀ {x₁ x₂ y₁ y₂} -> x₁ ≈ x₂ -> x₁ ≈ y₁ -> y₁ ≈ y₂ -> x₂ ≈ y₂
    p ⟨ r ⟩ q = trans (sym p) (trans r q)

    _⟩_⟨_ : ∀ {x₁ x₂ y₁ y₂} -> x₁ ≈ x₂ -> x₂ ≈ y₂ -> y₁ ≈ y₂ -> x₁ ≈ y₁
    p ⟩ r ⟨ q = sym p ⟨ r ⟩ sym q

record IsIEquivalence {ι α β} {I : Set ι} (A : I -> Set α) (_≈_ : ∀ {i} -> A i -> A i -> Set β)
                      : Set (ι ⊔ α ⊔ β) where
  field
    refl  : ∀ {i} {x     : A i} -> x ≈ x
    sym   : ∀ {i} {x y   : A i} -> x ≈ y -> y ≈ x
    trans : ∀ {i} {x y z : A i} -> x ≈ y -> y ≈ z -> x ≈ z

  module ITools where
    infix  2 _⟨_⟩_ _⟩_⟨_
    infixl 3 _⋯_

    _⋯_ = trans

    left  : ∀ {i} {x y z : A i} -> x ≈ y -> z ≈ y -> x ≈ z
    left  p q = trans p (sym q)

    right : ∀ {i} {x y z : A i} -> x ≈ y -> x ≈ z -> y ≈ z
    right p q = trans (sym p) q

    _⟨_⟩_ : ∀ {i} {x₁ x₂ y₁ y₂ : A i} -> x₁ ≈ x₂ -> x₁ ≈ y₁ -> y₁ ≈ y₂ -> x₂ ≈ y₂
    p ⟨ r ⟩ q = trans (sym p) (trans r q)

    _⟩_⟨_ : ∀ {i} {x₁ x₂ y₁ y₂ : A i} -> x₁ ≈ x₂ -> x₂ ≈ y₂ -> y₁ ≈ y₂ -> x₁ ≈ y₁
    p ⟩ r ⟨ q = sym p ⟨ r ⟩ sym q

record IsHEquivalence {ι α β} {I : Set ι} (A : I -> Set α) (_≈_ : ∀ {i j} -> A i -> A j -> Set β)
                      : Set (ι ⊔ α ⊔ β) where
  field
    refl  : ∀ {i}     {x : A i}                     -> x ≈ x
    sym   : ∀ {i j}   {x : A i} {y : A j}           -> x ≈ y -> y ≈ x
    trans : ∀ {i j k} {x : A i} {y : A j} {z : A k} -> x ≈ y -> y ≈ z -> x ≈ z

  module HTools where
    infix 2 _⟨_⟩_ _⟩_⟨_
    infixl 3 _⋯_

    _⋯_ = trans

    _⟨_⟩_ : ∀ {i₁ i₂ j₁ j₂} {x₁ : A i₁} {x₂ : A i₂} {y₁ : A j₁} {y₂ : A j₂}
          -> x₁ ≈ x₂ -> x₁ ≈ y₁ -> y₁ ≈ y₂ -> x₂ ≈ y₂
    p ⟨ r ⟩ q = trans (sym p) (trans r q)

    _⟩_⟨_ : ∀ {i₁ i₂ j₁ j₂} {x₁ : A i₁} {x₂ : A i₂} {y₁ : A j₁} {y₂ : A j₂}
          -> x₁ ≈ x₂ -> x₂ ≈ y₂ -> y₁ ≈ y₂ -> x₁ ≈ y₁
    p ⟩ r ⟨ q = sym p ⟨ r ⟩ sym q

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

  open IsIEquivalence isIEquivalence public

record HSetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
  infix 4 _≈_
  
  field
    _≈_            : ∀ {i j} -> A i -> A j -> Set β
    isHEquivalence : IsHEquivalence A _≈_

  open IsHEquivalence isHEquivalence public

ISetoid₂ : ∀ {ι₁ ι₂ α} {I₁ : Set ι₁} {I₂ : I₁ -> Set ι₂} (A : ∀ i₁ -> I₂ i₁ -> Set α) β
         -> Set (ι₁ ⊔ ι₂ ⊔ α ⊔ suc β)
ISetoid₂ A = ISetoid (uncurry A)

module Setoid¹ {α β} {A : Set α} (setoid : Setoid A β) where
  open Setoid setoid renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public

module Setoid² {α β} {A : Set α} (setoid : Setoid A β) where
  open Setoid setoid renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public

module ISetoid¹ {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open ISetoid isetoid renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public

module ISetoid² {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open ISetoid isetoid renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public

module HSetoid¹ {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open HSetoid hsetoid renaming (_≈_ to _≈₁_; refl to refl₁; sym to sym₁; trans to trans₁) public

module HSetoid² {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open HSetoid hsetoid renaming (_≈_ to _≈₂_; refl to refl₂; sym to sym₂; trans to trans₂) public

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

module HEqReasoning {ι α β} {I : Set ι} {A : I -> Set α} (hsetoid : HSetoid A β) where
  open HSetoid hsetoid

  infix  4 _IsRelatedTo_
  infix  1 begin_
  infixr 2 _→⟨_⟩_ _←⟨_⟩_
  infix  3 _∎
  
  record _IsRelatedTo_ {i j} (x : A i) (y : A j) : Set β where
    constructor relTo
    field x≈y : x ≈ y

  begin_ : ∀ {i j} {x : A i} {y : A j} -> x IsRelatedTo y -> x ≈ y
  begin (relTo x≈y) = x≈y

  _→⟨_⟩_ : ∀ {i j k} {y : A j} {z : A k} -> (x : A i) -> x ≈ y -> y IsRelatedTo z -> x IsRelatedTo z
  x →⟨ x≈y ⟩ (relTo y≈z) = relTo (trans x≈y y≈z)

  _←⟨_⟩_ : ∀ {i j k} {y : A j} {z : A k} -> (x : A i) -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  x ←⟨ y≈x ⟩ y-irt-z = x →⟨ sym y≈x ⟩ y-irt-z

  _∎ : ∀ {i} -> (x : A i) -> x IsRelatedTo x
  x ∎ = relTo refl

module IEqReasoning {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open module I = ISetoid isetoid; open Hetero isetoid
  private open module HER = HEqReasoning hsetoid hiding (begin_; _→⟨_⟩_; _←⟨_⟩_) public

  infix  1 begin_
  infixr 2 _→⟨_⟩_ _←⟨_⟩_

  begin_ : ∀ {i} {x y : A i} -> x IsRelatedTo y -> x ≈ y
  begin x-irt-y = homo (HER.begin x-irt-y)

  _→⟨_⟩_ : ∀ {i k} {y : A i} {z : A k} -> (x : A i) -> x ≈ y -> y IsRelatedTo z -> x IsRelatedTo z
  x →⟨ x≈y ⟩ y-irt-z = x HER.→⟨ hetero x≈y ⟩ y-irt-z

  _←⟨_⟩_ : ∀ {i k} {y : A i} {z : A k} -> (x : A i) -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  x ←⟨ y≈x ⟩ y-irt-z = x →⟨ I.sym y≈x ⟩ y-irt-z

module EqReasoning {α β} {A : Set α} (setoid : Setoid A β) where
  open import Data.Unit.Base
  open Setoid setoid; open Indexed setoid; open IEqReasoning {I = ⊤} isetoid public

module MixedEqReasoning {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open Hetero isetoid; open HEqReasoning hsetoid public

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

≡-Setoid : ∀ {α} {A : Set α} -> Setoid A α
≡-Setoid = record
  { _≈_           = _≡_
  ; isEquivalence = record
      { refl  = PE.refl
      ; sym   = PE.sym
      ; trans = PE.trans
      }
  }

≡-ISetoid : ∀ {ι α} {I : Set ι} {A : I -> Set α} -> ISetoid A α
≡-ISetoid = record
  { _≈_            = _≡_
  ; isIEquivalence = record
      { refl  = PE.refl
      ; sym   = PE.sym
      ; trans = PE.trans
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
  open HEquality

  test : ∀ n m -> (Fin (ℕ.suc n + m) ∋ Fin.zero) ≅ (Fin (ℕ.suc m + n) ∋ Fin.zero)
  test n m rewrite +-comm n m = refl
