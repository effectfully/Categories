open import Categories.Category

module Categories.Category.CCC {α β γ} (C : Category α β γ) where

open import Categories.Object C

record CCC : Set (α ⊔ β ⊔ γ) where
  field
    terminal       : Terminal
    binaryProducts : BinaryProducts
    exponentials   : Exponentials binaryProducts

  module Internal where
    open Category C
    open Terminal terminal
    open ProductTools binaryProducts
    open ExponentialTools exponentials

    infixr 7 _&_
    infixr 5 _↦_
    infix  4 _⊢₁_

    Type : Set α
    Type = Obj

    ⋆ : Type
    ⋆ = Ob

    _&_ : Type -> Type -> Type
    _&_ = _×_

    _⊢₁_ : Type -> Type -> Set β
    _⊢₁_ = _⇒_

    unit : ∀ {σ} -> σ ⊢₁ ⋆
    unit = ↝

    _[_]₁ : ∀ {σ τ ν} -> τ ⊢₁ ν -> σ ⊢₁ τ -> σ ⊢₁ ν
    _[_]₁ = _∘_
    
    pair : ∀ {σ τ ν} -> σ ⊢₁ τ -> σ ⊢₁ ν -> σ ⊢₁ τ & ν
    pair = ⟨_,_⟩

    fst : ∀ {σ τ} -> σ & τ ⊢₁ σ
    fst = π¹

    snd : ∀ {σ τ} -> σ & τ ⊢₁ τ
    snd = π²

    _↦_ : Type -> Type -> Type
    _↦_ = flip _^_

    apply : ∀ {σ τ} -> (σ ↦ τ) & σ ⊢₁ τ
    apply = eval

    lcurry : ∀ {σ τ ν} -> σ & τ ⊢₁ ν -> σ ⊢₁ τ ↦ ν
    lcurry = curr
