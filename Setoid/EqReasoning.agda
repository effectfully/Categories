module Categories.Setoid.EqReasoning where

open import Categories.Setoid.Equivalence
open import Categories.Setoid.Setoid

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
  x →⟨ x≈y ⟩ (relTo y≈z) = relTo (htrans x≈y y≈z)

  _←⟨_⟩_ : ∀ {i j k} {y : A j} {z : A k} -> (x : A i) -> y ≈ x -> y IsRelatedTo z -> x IsRelatedTo z
  x ←⟨ y≈x ⟩ y-irt-z = x →⟨ hsym y≈x ⟩ y-irt-z

  _∎ : ∀ {i} -> (x : A i) -> x IsRelatedTo x
  x ∎ = relTo hrefl

module IEqReasoning {ι α β} {I : Set ι} {A : I -> Set α} (isetoid : ISetoid A β) where
  open module I = ISetoid isetoid; open Just-Hetero isetoid
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
  open Just-Hetero isetoid; open HEqReasoning hsetoid public
