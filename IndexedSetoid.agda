module Categories.IndexedSetoid where

open import Level
open import Function

infixr 10 _%
_% = _∘_

record IsHeteroEquivalence {ι α β} {I : Set ι} (A : I -> Set α)
                           (_≈_ : ∀ {i j} -> A i -> A j -> Set β)
                           : Set (ι ⊔ α ⊔ β) where
  field
    hrefl  : ∀ {i}     {x : A i}                     -> x ≈ x
    hsym   : ∀ {i j}   {x : A i} {y : A j}           -> x ≈ y -> y ≈ x
    htrans : ∀ {i j k} {x : A i} {y : A j} {z : A k} -> x ≈ y -> y ≈ z -> x ≈ z

record IsIndexedEquivalence {ι α β} {I : Set ι} (A : I -> Set α)
                            (_≈_ : ∀ {i} -> A i -> A i -> Set β)
                            : Set (ι ⊔ α ⊔ β) where
  field
    irefl  : ∀ {i} {x     : A i} -> x ≈ x
    isym   : ∀ {i} {x y   : A i} -> x ≈ y -> y ≈ x
    itrans : ∀ {i} {x y z : A i} -> x ≈ y -> y ≈ z -> x ≈ z

record HeteroSetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
  infix 4 _≈_
  
  field
    _≈_                 : ∀ {i j} -> A i -> A j -> Set β
    isHeteroEquivalence : IsHeteroEquivalence A _≈_

  open IsHeteroEquivalence isHeteroEquivalence public

record IndexedSetoid {ι α} {I : Set ι} (A : I -> Set α) β : Set (ι ⊔ α ⊔ suc β) where
  infix 4 _≈_
  
  field
    _≈_                  : ∀ {i} -> A i -> A i -> Set β
    isIndexedEquivalence : IsIndexedEquivalence A _≈_

  open IsIndexedEquivalence isIndexedEquivalence public

module Hetero {ι α β} {I : Set ι} {A : I -> Set α} (indexedSetoid : IndexedSetoid A β) where
  open IndexedSetoid indexedSetoid

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

  heteroSetoid : HeteroSetoid A β
  heteroSetoid = record
    { _≈_                 = λ x y -> x ≋ y
    ; isHeteroEquivalence = record
        { hrefl  = hetero irefl
        ; hsym   = hlift₁ (hetero ∘ isym)
        ; htrans = hlift₂ (hetero % ∘ itrans)
        }
    }

  open HeteroSetoid heteroSetoid public hiding (_≈_)

module HeteroEqReasoning {ι α β} {I : Set ι} {A : I -> Set α}
                         (heteroSetoid : HeteroSetoid A β) where
  open HeteroSetoid heteroSetoid

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
  x →⟨ x≈y ⟩ (relTo y≈z) = relTo (htrans x≈y y≈z)

  _←⟨_⟩_ : ∀ {i j k} {y : A j} {z : A k} -> (x : A i) -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  x ←⟨ y≈x ⟩ y-irt-z = x →⟨ hsym y≈x ⟩ y-irt-z

  _∎ : ∀ {i} -> (x : A i) -> x IsRelatedTo x
  x ∎ = relTo hrefl

module IndexedEqReasoning {ι α β} {I : Set ι} {A : I -> Set α}
                          (indexedSetoid : IndexedSetoid A β) where
  open IndexedSetoid indexedSetoid
  open Hetero indexedSetoid
  private open module HER = HeteroEqReasoning heteroSetoid
                              hiding (begin_; _→⟨_⟩_; _←⟨_⟩_) public

  infix  1 begin_
  infixr 2 _→⟨_⟩_ _←⟨_⟩_

  begin_ : ∀ {i} {x y : A i} -> x IsRelatedTo y -> x ≈ y
  begin (relTo x≋y) = homo x≋y

  _→⟨_⟩_ : ∀ {i k} {y : A i} {z : A k} -> (x : A i) -> x ≈ y -> y IsRelatedTo z -> x IsRelatedTo z
  x →⟨ x≈y ⟩ y-irt-z = x HER.→⟨ hetero x≈y ⟩ y-irt-z

  _←⟨_⟩_ : ∀ {i k} {y : A i} {z : A k} -> (x : A i) -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  x ←⟨ y≈x ⟩ y-irt-z = x →⟨ isym y≈x ⟩ y-irt-z

module MixedEqReasoning {ι α β} {I : Set ι} {A : I -> Set α}
                        (indexedSetoid : IndexedSetoid A β) where
  open Hetero indexedSetoid; open HeteroEqReasoning heteroSetoid public
