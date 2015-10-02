module Categories.STLC.Properties.NbE where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core
open import Categories.STLC.Core.NbE
open import Categories.STLC.Properties
open import Categories.STLC.Ext

mutual
  renⁿᵉ-idˢ : ∀ {Γ σ} (t : Γ ⊢ⁿᵉ σ) -> renⁿᵉ idˢ t ≡ t
  renⁿᵉ-idˢ (varⁿᵉ v) = cong varⁿᵉ (renᵛ-idˢ v)
  renⁿᵉ-idˢ (f ·ⁿᵉ x) = cong₂ _·ⁿᵉ_ (renⁿᵉ-idˢ f) (renⁿᶠ-idˢ x)

  renⁿᶠ-idˢ : ∀ {Γ σ} (t : Γ ⊢ⁿᶠ σ) -> renⁿᶠ idˢ t ≡ t
  renⁿᶠ-idˢ (neⁿᶠ t) = cong neⁿᶠ (renⁿᵉ-idˢ t)
  renⁿᶠ-idˢ (ƛⁿᶠ  b) = cong ƛⁿᶠ_ (renⁿᶠ-idˢ b)

mutual
  renⁿᵉ-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᵉ σ)
          -> renⁿᵉ (κ ∘ˢ ι) t ≡ renⁿᵉ κ (renⁿᵉ ι t)
  renⁿᵉ-∘ {κ = κ} (varⁿᵉ v) = cong varⁿᵉ (renᵛ-∘ κ _ v)
  renⁿᵉ-∘         (f ·ⁿᵉ x) = cong₂ _·ⁿᵉ_ (renⁿᵉ-∘ f) (renⁿᶠ-∘ x)

  renⁿᶠ-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᶠ σ)
          -> renⁿᶠ (κ ∘ˢ ι) t ≡ renⁿᶠ κ (renⁿᶠ ι t)
  renⁿᶠ-∘ (neⁿᶠ t) = cong neⁿᶠ (renⁿᵉ-∘ t)
  renⁿᶠ-∘ (ƛⁿᶠ  b) = cong ƛⁿᶠ_ (renⁿᶠ-∘ b)

mutual
  embⁿᵉ-renⁿᵉ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᵉ σ)
              -> embⁿᵉ (renⁿᵉ ι t) ≡ ren ι (embⁿᵉ t)
  embⁿᵉ-renⁿᵉ (varⁿᵉ v) = refl
  embⁿᵉ-renⁿᵉ (f ·ⁿᵉ x) = cong₂ _·_ (embⁿᵉ-renⁿᵉ f) (embⁿᶠ-renⁿᶠ x)

  embⁿᶠ-renⁿᶠ : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᶠ σ)
              -> embⁿᶠ (renⁿᶠ ι t) ≡ ren ι (embⁿᶠ t)
  embⁿᶠ-renⁿᶠ (neⁿᶠ t) = embⁿᵉ-renⁿᵉ t
  embⁿᶠ-renⁿᶠ (ƛⁿᶠ  b) = cong ƛ (embⁿᶠ-renⁿᶠ b)

renˢᵉᵐ-idˢ : ∀ {σ Γ} (x : ⟦ σ ⟧ᵀ Γ) -> renˢᵉᵐ idˢ x ≡ x
renˢᵉᵐ-idˢ {⋆    } t = renⁿᵉ-idˢ t
renˢᵉᵐ-idˢ {σ ⇒ τ} f = extᵢ ext λ x -> cong f idʳˢ

renˢᵉᵐ-∘ : ∀ {σ Γ Δ Θ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (x : ⟦ σ ⟧ᵀ Γ)
         -> renˢᵉᵐ (κ ∘ˢ ι) x ≡ renˢᵉᵐ κ (renˢᵉᵐ ι x)
renˢᵉᵐ-∘ {⋆    } t = renⁿᵉ-∘ t
renˢᵉᵐ-∘ {σ ⇒ τ} f = extᵢ ext λ π -> cong f (sym (assocˢ π _ _))

↑-varⁿᵉ-renᵛ : ∀ {σ Γ Δ} {ι : Γ ⊆ Δ} (v : σ ∈ Γ)
            -> ↑ (varⁿᵉ (renᵛ ι v)) ≡ renˢᵉᵐ ι (↑ (varⁿᵉ v))
↑-varⁿᵉ-renᵛ {⋆    } v = refl
↑-varⁿᵉ-renᵛ {σ ⇒ τ} v = extᵢ ext λ κ -> ext λ x -> cong (λ f -> ↑ (varⁿᵉ f ·ⁿᵉ ↓ x))
                                                        (sym (renᵛ-∘ κ _ v))

↑-renⁿᵉ : ∀ {σ Γ Δ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᵉ σ)
        -> ↑ (renⁿᵉ ι t) ≡ renˢᵉᵐ ι (↑ t)
↑-renⁿᵉ {⋆    } t = refl
↑-renⁿᵉ {σ ⇒ τ} f = extᵢ ext λ κ -> ext λ x -> cong (λ f -> ↑ (f ·ⁿᵉ ↓ x)) (sym (renⁿᵉ-∘ f))

-- ↓-renˢᵉᵐ : ∀ {σ Γ Δ} {ι : Γ ⊆ Δ} (x : ⟦ σ ⟧ᵀ Γ)
--          -> ↓ (renˢᵉᵐ ι x) ≡ renⁿᶠ ι (↓ x)
-- ↓-renˢᵉᵐ {⋆    } t = refl
-- ↓-renˢᵉᵐ {σ ⇒ τ} f = cong ƛⁿᶠ_ (trans (cong ↓ (trans (cong (λ ι -> f (skip ι) _) idˡˢ)
--                                                      {!!}))
--                                       (↓-ren (f _ _)))

▷-renᵛ : ∀ {Γ Δ Θ Ξ σ τ} {κ : Θ ⊆ Ξ} {ι : Γ ⊆ Δ} {ρ : Δ ↦ Θ} (x : ⟦ σ ⟧ᵀ Ξ) (v : τ ∈ Γ ▻ σ)
      -> (renˢᵉᵐ κ ∘ ρ ∘ renᵛ ι ▷ x) v ≡ (renˢᵉᵐ κ ∘ ρ ▷ x) (renᵛ (keep ι) v)
▷-renᵛ x  vz    = refl
▷-renᵛ x (vs v) = refl

⟦⟧-renᵛ-ren : ∀ {Γ Δ Θ σ} {ι : Γ ⊆ Δ} {ρ : Δ ↦ Θ} (t : Γ ⊢ σ)
           -> ⟦ t ⟧ (ρ ∘ renᵛ ι) ≡ ⟦ ren ι t ⟧ ρ
⟦⟧-renᵛ-ren             (var v) = refl
⟦⟧-renᵛ-ren             (ƛ b  ) = extᵢ ext λ κ -> ext λ x -> trans (cong ⟦ b ⟧ (extᵢ ext ▷-renᵛ x))
                                                                  (⟦⟧-renᵛ-ren b)
⟦⟧-renᵛ-ren {ι = ι} {ρ} (f · x) rewrite ⟦⟧-renᵛ-ren {ι = ι} {ρ} f
                               |       ⟦⟧-renᵛ-ren {ι = ι} {ρ} x
                               = refl

⟦⟧-resp-≈ : ∀ {Γ Δ σ} {ρ χ : Γ ↦ Δ} (t : Γ ⊢ σ)
          -> (∀ {σ} (v : σ ∈ Γ) -> ρ v ≡ χ v) -> ⟦ t ⟧ ρ ≡ ⟦ t ⟧ χ
⟦⟧-resp-≈ t p = cong ⟦ t ⟧ (extᵢ ext p)
