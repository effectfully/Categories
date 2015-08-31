module Categories.Setoid.Equivalence where

open import Categories.Utilities.Prelude
open import Categories.Utilities.Product

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

  module HEqTools where
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

comap∀ⁱᵉₑ : ∀ {ι₁ ι₂ α₁ α₂ β γ} {I₁ : Set ι₁} {I₂ : Set ι₂}
              {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂} {k : I₁ -> I₂}
              {B : I₁ -> Set β} {_≈_ : ∀ {i₂} -> A₂ i₂ -> A₂ i₂ -> Set γ}
          -> (f : ∀ {i₁} -> B i₁ -> A₁ i₁ -> A₂ (k i₁))
          -> IsIEquivalence A₂  _≈_
          -> IsIEquivalence A₁ (λ x y -> ∀ z -> f z x ≈ f z y)
comap∀ⁱᵉₑ f isIEquivalence = record
  { refl  = λ     z -> refl
  ; sym   = λ p   z -> sym   (p z)
  ; trans = λ p q z -> trans (p z) (q z)
  } where open IsIEquivalence isIEquivalence

comap∀ⁱᵉ : ∀ {ι₁ ι₂ α₁ α₂ β γ} {I₁ : Set ι₁} {I₂ : Set ι₂}
             {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂} {k : I₁ -> I₂}
             {B : I₁ -> Set β} {_≈_ : ∀ {i₂} -> A₂ i₂ -> A₂ i₂ -> Set γ}
         -> (f : ∀ {i₁} -> B i₁ -> A₁ i₁ -> A₂ (k i₁))
         -> IsIEquivalence A₂  _≈_
         -> IsIEquivalence A₁ (λ x y -> ∀ {z} -> f z x ≈ f z y)
comap∀ⁱᵉ f isIEquivalence = record
  { refl  =          refl
  ; sym   = λ p   -> sym   p 
  ; trans = λ p q -> trans p q
  } where open IsIEquivalence isIEquivalence

comapⁱᵉ : ∀ {ι₁ ι₂ α₁ α₂ β} {I₁ : Set ι₁} {I₂ : Set ι₂}
            {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂} {k : I₁ -> I₂}
            {_≈_ : ∀ {i₂} -> A₂ i₂ -> A₂ i₂ -> Set β}
        -> (f : ∀ {i₁} -> A₁ i₁ -> A₂ (k i₁))
        -> IsIEquivalence A₂  _≈_
        -> IsIEquivalence A₁ (λ x y -> f x ≈ f y)
comapⁱᵉ f isIEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  } where open IsIEquivalence isIEquivalence

coerceⁱᵉ : ∀ {ι₁ ι₂ α β} {I₁ : Set ι₁} {I₂ : Set ι₂} {A : I₂ -> Set α} {k : I₁ -> I₂}
             {_≈_ : ∀ {i₂} -> A i₂ -> A i₂ -> Set β}
         -> IsIEquivalence A  _≈_ -> IsIEquivalence (A ∘′ k) _≈_
coerceⁱᵉ = comapⁱᵉ id′

module _ {α β} {A : Set α} {_≈_ : A -> A -> Set β}
         (isEquivalence : IsEquivalence _≈_) where
  module IsEquivalence₁ = IsEquivalence isEquivalence
    renaming (refl to refl₁; sym to sym₁; trans to trans₁; module EqTools to EqTools₁)

  module IsEquivalence₂ = IsEquivalence isEquivalence
    renaming (refl to refl₂; sym to sym₂; trans to trans₂; module EqTools to EqTools₂)

  module IsEquivalence₃ = IsEquivalence isEquivalence
    renaming (refl to refl₃; sym to sym₃; trans to trans₃; module EqTools to EqTools₃)

module _ {ι α β} {I : Set ι} {A : I -> Set α} {_≈_ : ∀ {i} -> A i -> A i -> Set β}
         (isIEquivalence : IsIEquivalence A _≈_) where
  module IsIEquivalence₁ = IsIEquivalence isIEquivalence
    renaming (refl to refl₁; sym to sym₁; trans to trans₁; module EqTools to EqTools₁)

  module IsIEquivalence₂ = IsIEquivalence isIEquivalence
    renaming (refl to refl₂; sym to sym₂; trans to trans₂; module EqTools to EqTools₂)

  module IsIEquivalence₃ = IsIEquivalence isIEquivalence
    renaming (refl to refl₃; sym to sym₃; trans to trans₃; module EqTools to EqTools₃)

module _ {ι α β} {I : Set ι} {A : I -> Set α} {_≈_ : ∀ {i j} -> A i -> A j -> Set β}
         (isHEquivalence : IsHEquivalence A _≈_) where
  module IsHEquivalence₁ = IsHEquivalence isHEquivalence
    renaming (hrefl to hrefl₁; hsym to  hsym₁; htrans to htrans₁; module HEqTools to HEqTools₁)
                                                 
  module IsHEquivalence₂ = IsHEquivalence isHEquivalence
    renaming (hrefl to hrefl₂; hsym to  hsym₂; htrans to htrans₂; module HEqTools to HEqTools₂)

  module IsHEquivalence₃ = IsHEquivalence isHEquivalence
    renaming (hrefl to hrefl₃; hsym to  hsym₃; htrans to htrans₃; module HEqTools to HEqTools₃)

_×ⁱᵉ_ : ∀ {ι₁ ι₂ ι₃ α₁ α₂ β₁ β₂} {I₁ : Set ι₁} {I₂ : Set ι₂} {I₃ : Set ι₃}
          {A₁ : I₁ -> Set α₁} {A₂ : I₂ -> Set α₂} {k₁ : I₃ -> I₁} {k₂ : I₃ -> I₂}
          {_≈₁_ : ∀ {i} -> A₁ i -> A₁ i -> Set β₁} {_≈₂_ : ∀ {i} -> A₂ i -> A₂ i -> Set β₂}
      -> IsIEquivalence A₁ _≈₁_
      -> IsIEquivalence A₂ _≈₂_
      -> IsIEquivalence (λ i -> A₁ (k₁ i) ×ₚ A₂ (k₂ i)) (_≈₁_ <×> _≈₂_)
E₁ ×ⁱᵉ E₂ = record
  { refl  = refl₁ , refl₂
  ; sym   = map sym₁ sym₂
  ; trans = zip trans₁ trans₂
  } where open IsIEquivalence₁ E₁; open IsIEquivalence₂ E₂
