open import Categories.Category

module Categories.Category.CCC {α β γ} (C : Category α β γ) where

open import Data.Nat.Base hiding (_⊔_)

open import Categories.Utilities.Replicate
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
    infix  4 _⊢_
    infixr 5 ƛ_
    infixl 6 _·_

    Type : Set α
    Type = Obj

    ⋆ : Type
    ⋆ = Ob

    _↦_ : Type -> Type -> Type
    _↦_ = flip _^_

    _&_ : Type -> Type -> Type
    _&_ = _×_

    _⊢_ : Type -> Type -> Set β
    _⊢_ = _⇒_

    unit : ∀ {Γ} -> Γ ⊢ ⋆
    unit = ↝

    ƛ_ : ∀ {Γ σ τ} -> Γ & σ ⊢ τ -> Γ ⊢ σ ↦ τ
    ƛ_ = curr
    
    pair : ∀ {Γ σ τ} -> Γ ⊢ σ -> Γ ⊢ τ -> Γ ⊢ σ & τ
    pair = ⟨_,_⟩

    _[_] : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Δ ⊢ Γ -> Δ ⊢ σ
    _[_] = _∘_

    _·_ : ∀ {Γ σ τ} -> Γ ⊢ σ ↦ τ -> Γ ⊢ σ -> Γ ⊢ τ
    f · x = eval [ pair f x ]

    fst : ∀ {Γ σ τ} -> Γ ⊢ σ & τ -> Γ ⊢ σ
    fst p = π¹ [ p ]

    snd : ∀ {Γ σ τ} -> Γ ⊢ σ & τ -> Γ ⊢ τ
    snd p = π² [ p ]

    ↑ : ∀ {Γ σ} -> Γ & σ ⊢ Γ
    ↑ = π¹

    vz : ∀ {Γ σ} -> Γ & σ ⊢ σ
    vz = π²

    shift : ∀ {Γ σ τ} -> Γ ⊢ σ -> Γ & τ ⊢ σ
    shift t = t [ ↑ ]

    var : ∀ {Δ σ} n {Γ : Replicate n Type} -> foldrʳ (flip _&_) (Δ & σ) Γ ⊢ σ
    var  0      = vz
    var (suc n) = shift (var n)

    I : ∀ {Γ σ} -> Γ ⊢ σ ↦ σ
    I = ƛ var 0

    A : ∀ {Γ σ τ} -> Γ ⊢ (σ ↦ τ) ↦ σ ↦ τ
    A = ƛ ƛ var 1 · var 0

    K : ∀ {Γ σ τ} -> Γ ⊢ σ ↦ τ ↦ σ
    K = ƛ ƛ var 1

    S : ∀ {Γ σ τ ν} -> Γ ⊢ (σ ↦ τ ↦ ν) ↦ (σ ↦ τ) ↦ σ ↦ ν
    S = ƛ ƛ ƛ var 2 · var 0 · (var 1 · var 0)
