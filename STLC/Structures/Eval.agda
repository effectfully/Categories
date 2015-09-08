module Categories.STLC.Structures.Eval where

open import Categories.Category
open import Categories.NaturalTransformation.Algebra
open import Categories.STLC.Core.Eval
open import Categories.STLC.Properties.Eval
open import Categories.STLC.Structures

Eval : N-Algebra Term 
Eval = record
  { Ob         = ⟦_⟧ᵀ
  ; str        = λ ρ t -> ⟦ t ⟧ ρ
  ; ηʳ         = λ v -> prefl
  ; str-∘      = ⟦⟧-ren-sub
  ; str-resp-≈ = λ p t -> ⟦⟧-resp-≈ t p
  }
