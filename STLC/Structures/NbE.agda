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

Subⁿᵉ : Functor (OPE Type) (ISets Type)
Subⁿᵉ = record
  { F·       = _⊢ⁿᵉ_
  ; F⇒       = λ ι t -> subⁿᵉ ι t
  ; F-id     = subⁿᵉ-idˢ
  ; F-∘      = subⁿᵉ-∘
  ; F-resp-≈ = λ p t -> cong (flip subⁿᵉ t) p
  }

Subⁿᶠ : Functor (OPE Type) (ISets Type)
Subⁿᶠ = record
  { F·       = _⊢ⁿᶠ_
  ; F⇒       = λ ι t -> subⁿᶠ ι t
  ; F-id     = subⁿᶠ-idˢ
  ; F-∘      = subⁿᶠ-∘
  ; F-resp-≈ = λ p t -> cong (flip subⁿᶠ t) p
  }

Subˢᵉᵐ : Functor (OPE Type) (ISets Type)
Subˢᵉᵐ = record
  { F·       = flip ⟦_⟧ᵀ
  ; F⇒       = λ ι x -> subˢᵉᵐ ι x
  ; F-id     = subˢᵉᵐ-idˢ
  ; F-∘      = subˢᵉᵐ-∘
  ; F-resp-≈ = λ p x -> cong (flip subˢᵉᵐ x) p
  }

Embⁿᵉ : NaturalTransformation Subⁿᵉ Sub
Embⁿᵉ = record
  { η          = embⁿᵉ
  ; naturality = embⁿᵉ-subⁿᵉ
  }

Embⁿᶠ : NaturalTransformation Subⁿᶠ Sub
Embⁿᶠ = record
  { η          = embⁿᶠ
  ; naturality = embⁿᶠ-subⁿᶠ
  }

Varⁿᵉ : NaturalTransformation Ren Subⁿᵉ
Varⁿᵉ = record
  { η          = varⁿᵉ
  ; naturality = λ v -> prefl
  }

Neⁿᶠ : NaturalTransformation Subⁿᵉ Subⁿᶠ
Neⁿᶠ = record
  { η          = neⁿᶠ
  ; naturality = λ t -> prefl
  }

Sem : NaturalTransformation Ren Subˢᵉᵐ
Sem = record
  { η          = varˢᵉᵐ
  ; naturality = ↑-varⁿᵉ-ren
  }

Reflect : NaturalTransformation Subⁿᵉ Subˢᵉᵐ
Reflect = record
  { η          = ↑
  ; naturality = ↑-subⁿᵉ
  }

-- Reify : NaturalTransformation Subˢᵉᵐ Subⁿᶠ
-- Reify = record
--   { η          = ↓
--   ; naturality = ↓-subˢᵉᵐ
--   }

-- RRTerm : NaturalTransformation Ren Sub
-- RRTerm = Embⁿᶠ ∘ⁿ Reify ∘ⁿ Reflect ∘ⁿ Varⁿᵉ

Eval : Relative-N-Algebra Subˢᵉᵐ Term
Eval = record
  { str        = λ ρ t -> ⟦ t ⟧ ρ
  ; ηʳ         = λ v -> prefl
  ; str-∘₁     = ⟦⟧-ren-sub
  ; str-∘₂     = {!!}
  ; str-resp-≈ = λ p t -> ⟦⟧-resp-≈ t p
  }
