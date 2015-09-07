module Categories.STLC.Structures where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Algebra
open import Categories.Categories.Agda
open import Categories.STLC.STLC
open import Categories.STLC.Properties

Ren : Functor (OPE Type) (ISets Type)
Ren = record
  { F·       = flip _∈_
  ; F⇒       = λ ι v -> ren ι v
  ; F-id     = ren-idˢ
  ; F-∘      = λ {_ _ _ κ ι} -> ren-∘ κ ι
  ; F-resp-≈ = λ p v -> cong (flip ren v) p
  }

Sub : Functor (OPE Type) (ISets Type)
Sub = record
  { F·       = _⊢_
  ; F⇒       = λ ι t -> sub ι t
  ; F-id     = sub-idˢ
  ; F-∘      = sub-∘
  ; F-resp-≈ = λ p t -> cong (flip sub t) p
  }

Term : NaturalTransformation Ren Sub
Term = record
  { η          = var
  ; naturality = λ v -> prefl
  }

module Eval where
  open import Categories.STLC.Eval

  Semantics : N-Algebra Term 
  Semantics = record
    { Ob         = ⟦_⟧ᵀ
    ; str        = λ ρ t -> ⟦ t ⟧ ρ
    ; ηʳ         = λ v -> prefl
    ; str-∘      = ⟦⟧-ren-sub
    ; str-resp-≈ = λ p t -> {!!}
    }

module NbE where
  open import Categories.STLC.NbE

  Renˢᵉᵐ : Functor (OPE Type) (ISets Type)
  Renˢᵉᵐ = record
    { F·       = flip ⟦_⟧ᵀ
    ; F⇒       = λ ι x -> renˢᵉᵐ ι x
    ; F-id     = {!!}
    ; F-∘      = {!!}
    ; F-resp-≈ = {!!}
    }

  Sem : NaturalTransformation Ren Renˢᵉᵐ
  Sem = record
    { η          = varˢᵉᵐ
    ; naturality = {!!}
    }  
    
  Semantics : Relative-N-Algebra Term Sem
  Semantics = record
    { str        = λ ρ t -> ⟦ t ⟧ ρ
    ; ηʳ         = λ v -> prefl
    ; str-∘₁     = {!!}
    ; str-∘₂     = {!!}
    ; str-resp-≈ = λ p t -> {!!}
    }
