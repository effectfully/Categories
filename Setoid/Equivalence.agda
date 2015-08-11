module Categories.Setoid.Equivalence where

open import Level

record IsEquivalence {α β} {A : Set α} (_≈_ : A -> A -> Set β) : Set (α ⊔ β) where
  field
    refl  : ∀ {x}     -> x ≈ x
    sym   : ∀ {x y}   -> x ≈ y -> y ≈ x
    trans : ∀ {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

  module EqTools where
    infix  5 _⌈_⌉_ _⌊_⌋_
    infixl 6 _⋯_

    _⋯_ = trans

    left  : ∀ {x y z} -> x ≈ y -> z ≈ y -> x ≈ z
    left  p q = trans p (sym q)

    right : ∀ {x y z} -> x ≈ y -> x ≈ z -> y ≈ z
    right p q = trans (sym p) q

    _⌈_⌉_ : ∀ {x₁ x₂ y₁ y₂} -> x₁ ≈ x₂ -> x₁ ≈ y₁ -> y₁ ≈ y₂ -> x₂ ≈ y₂
    p ⌈ r ⌉ q = trans (sym p) (trans r q)

    _⌊_⌋_ : ∀ {x₁ x₂ y₁ y₂} -> x₁ ≈ x₂ -> x₂ ≈ y₂ -> y₁ ≈ y₂ -> x₁ ≈ y₁
    p ⌊ r ⌋ q = sym p ⌈ r ⌉ sym q

record IsIEquivalence {ι α β} {I : Set ι} (A : I -> Set α) (_≈_ : ∀ {i} -> A i -> A i -> Set β)
                      : Set (ι ⊔ α ⊔ β) where
  field
    refl  : ∀ {i} {x     : A i} -> x ≈ x
    sym   : ∀ {i} {x y   : A i} -> x ≈ y -> y ≈ x
    trans : ∀ {i} {x y z : A i} -> x ≈ y -> y ≈ z -> x ≈ z

  inst : ∀ i -> IsEquivalence (_≈_ {i})
  inst i = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }

  module EqTools where
    infix  5 _⌈_⌉_ _⌊_⌋_
    infixl 6 _⋯_

    _⋯_ = trans

    left  : ∀ {i} {x y z : A i} -> x ≈ y -> z ≈ y -> x ≈ z
    left  p q = trans p (sym q)

    right : ∀ {i} {x y z : A i} -> x ≈ y -> x ≈ z -> y ≈ z
    right p q = trans (sym p) q

    _⌈_⌉_ : ∀ {i} {x₁ x₂ y₁ y₂ : A i} -> x₁ ≈ x₂ -> x₁ ≈ y₁ -> y₁ ≈ y₂ -> x₂ ≈ y₂
    p ⌈ r ⌉ q = trans (sym p) (trans r q)

    _⌊_⌋_ : ∀ {i} {x₁ x₂ y₁ y₂ : A i} -> x₁ ≈ x₂ -> x₂ ≈ y₂ -> y₁ ≈ y₂ -> x₁ ≈ y₁
    p ⌊ r ⌋ q = sym p ⌈ r ⌉ sym q

record IsHEquivalence {ι α β} {I : Set ι} (A : I -> Set α) (_≈_ : ∀ {i j} -> A i -> A j -> Set β)
                      : Set (ι ⊔ α ⊔ β) where
  field
    hrefl  : ∀ {i}     {x : A i}                     -> x ≈ x
    hsym   : ∀ {i j}   {x : A i} {y : A j}           -> x ≈ y -> y ≈ x
    htrans : ∀ {i j k} {x : A i} {y : A j} {z : A k} -> x ≈ y -> y ≈ z -> x ≈ z

  hinst : ∀ i -> IsEquivalence (_≈_ {i} {i})
  hinst i = record
    { refl  = hrefl
    ; sym   = hsym
    ; trans = htrans
    }

  module EqTools where
    infix  5 _⌈_⌉_ _⌊_⌋_
    infixl 6 _⋯_

    _⋯_ = htrans

    left  : ∀ {i j k} {x : A i} {y : A j} {z : A k} -> x ≈ y -> z ≈ y -> x ≈ z
    left  p q = htrans p (hsym q)

    right : ∀ {i j k} {x : A i} {y : A j} {z : A k} -> x ≈ y -> x ≈ z -> y ≈ z
    right p q = htrans (hsym p) q

    _⌈_⌉_ : ∀ {i₁ i₂ j₁ j₂} {x₁ : A i₁} {x₂ : A i₂} {y₁ : A j₁} {y₂ : A j₂}
          -> x₁ ≈ x₂ -> x₁ ≈ y₁ -> y₁ ≈ y₂ -> x₂ ≈ y₂
    p ⌈ r ⌉ q = htrans (hsym p) (htrans r q)

    _⌊_⌋_ : ∀ {i₁ i₂ j₁ j₂} {x₁ : A i₁} {x₂ : A i₂} {y₁ : A j₁} {y₂ : A j₂}
          -> x₁ ≈ x₂ -> x₂ ≈ y₂ -> y₁ ≈ y₂ -> x₁ ≈ y₁
    p ⌊ r ⌋ q = hsym p ⌈ r ⌉ hsym q

module _ {α β} {A : Set α} {_≈_ : A -> A -> Set β}
         (isEquivalence : IsEquivalence _≈_) where
  module IsEquivalence₁ where
    open IsEquivalence isEquivalence renaming (refl to refl₁; sym to sym₁; trans to trans₁;
                                               module EqTools to EqTools₁) public

  module IsEquivalence₂ where
    open IsEquivalence isEquivalence renaming (refl to refl₂; sym to sym₂; trans to trans₂;
                                               module EqTools to EqTools₂) public

  module IsEquivalence₃ where
    open IsEquivalence isEquivalence renaming (refl to refl₃; sym to sym₃; trans to trans₃;
                                               module EqTools to EqTools₃) public

module _ {ι α β} {I : Set ι} {A : I -> Set α} {_≈_ : ∀ {i} -> A i -> A i -> Set β}
         (isIEquivalence : IsIEquivalence A _≈_) where
  module IsIEquivalence₁ where
    open IsIEquivalence isIEquivalence renaming (refl to refl₁; sym to sym₁; trans to trans₁;
                                                 module EqTools to EqTools₁) public

  module IsIEquivalence₂ where
    open IsIEquivalence isIEquivalence renaming (refl to refl₂; sym to sym₂; trans to trans₂;
                                                 module EqTools to EqTools₂) public

  module IsIEquivalence₃ where
    open IsIEquivalence isIEquivalence renaming (refl to refl₃; sym to sym₃; trans to trans₃;
                                                 module EqTools to EqTools₃) public

module _ {ι α β} {I : Set ι} {A : I -> Set α} {_≈_ : ∀ {i j} -> A i -> A j -> Set β}
         (isHEquivalence : IsHEquivalence A _≈_) where
  module IsHEquivalence₁ where
    open IsHEquivalence isHEquivalence renaming (hrefl to hrefl₁; hsym to  hsym₁; htrans to htrans₁;
                                                 module EqTools to EqTools₁) public
                                                 
  module IsHEquivalence₂ where
    open IsHEquivalence isHEquivalence renaming (hrefl to hrefl₂; hsym to  hsym₂; htrans to htrans₂;
                                                 module EqTools to EqTools₂) public

  module IsHEquivalence₃ where
    open IsHEquivalence isHEquivalence renaming (hrefl to hrefl₃; hsym to  hsym₃; htrans to htrans₃;
                                                 module EqTools to EqTools₃) public
