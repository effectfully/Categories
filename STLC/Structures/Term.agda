module Categories.STLC.Structures.Term where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Agda
open import Categories.STLC.Core
open import Categories.STLC.Properties
open import Categories.STLC.Structures.OPE

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
