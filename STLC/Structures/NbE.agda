module Categories.STLC.Structures.NbE where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.Algebra
open import Categories.Categories.Agda
open import Categories.STLC.Core
open import Categories.STLC.Core.NbE
open import Categories.STLC.Properties.NbE
open import Categories.STLC.Structures

Renˢᵉᵐ : Functor (OPE Type) (ISets Type)
Renˢᵉᵐ = record
  { F·       = flip ⟦_⟧ᵀ
  ; F⇒       = λ ι x -> renˢᵉᵐ ι x
  ; F-id     = renˢᵉᵐ-idˢ
  ; F-∘      = renˢᵉᵐ-∘
  ; F-resp-≈ = λ p x -> cong (flip renˢᵉᵐ x) p
  }

Sem : NaturalTransformation Ren Renˢᵉᵐ
Sem = record
  { η          = varˢᵉᵐ
  ; naturality = ren-renˢᵉᵐ
  }
    
Eval : Relative-N-Algebra Term Sem
Eval = record
  { str        = λ ρ t -> ⟦ t ⟧ ρ
  ; ηʳ         = λ v -> prefl
  ; str-∘₁     = ⟦⟧-ren-sub
  ; str-∘₂     = {!!}
  ; str-resp-≈ = λ p t -> ⟦⟧-resp-≈ t p
  }
