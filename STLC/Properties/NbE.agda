module Categories.STLC.Properties.NbE where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core
open import Categories.STLC.Core.NbE
open import Categories.STLC.Properties
open import Categories.STLC.Ext

mutual
  renⁿᵉ-idˢ : ∀ {Γ σ} (t : Γ ⊢ⁿᵉ σ) -> renⁿᵉ idˢ t ≡ t
  renⁿᵉ-idˢ (varⁿᵉ v) = cong varⁿᵉ (ren-idˢ v)
  renⁿᵉ-idˢ (f ·ⁿᵉ x) = cong₂ _·ⁿᵉ_ (renⁿᵉ-idˢ f) (renⁿᶠ-idˢ x)

  renⁿᶠ-idˢ : ∀ {Γ σ} (t : Γ ⊢ⁿᶠ σ) -> renⁿᶠ idˢ t ≡ t
  renⁿᶠ-idˢ (neⁿᶠ t) = cong neⁿᶠ (renⁿᵉ-idˢ t)
  renⁿᶠ-idˢ (ƛⁿᶠ  b) = cong ƛⁿᶠ_ (renⁿᶠ-idˢ b)

renˢᵉᵐ-idˢ : ∀ {σ Γ} (x : ⟦ σ ⟧ᵀ Γ) -> renˢᵉᵐ idˢ x ≡ x
renˢᵉᵐ-idˢ {⋆    } t = renⁿᵉ-idˢ t
renˢᵉᵐ-idˢ {σ ⇒ τ} f = extᵢ ext λ x -> cong f idʳˢ

mutual
  renⁿᵉ-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᵉ σ)
          -> renⁿᵉ (κ ∘ˢ ι) t ≡ renⁿᵉ κ (renⁿᵉ ι t)
  renⁿᵉ-∘ {κ = κ} (varⁿᵉ v) = cong varⁿᵉ (ren-∘ κ _ v)
  renⁿᵉ-∘         (f ·ⁿᵉ x) = cong₂ _·ⁿᵉ_ (renⁿᵉ-∘ f) (renⁿᶠ-∘ x)

  renⁿᶠ-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᶠ σ)
          -> renⁿᶠ (κ ∘ˢ ι) t ≡ renⁿᶠ κ (renⁿᶠ ι t)
  renⁿᶠ-∘ (neⁿᶠ t) = cong neⁿᶠ (renⁿᵉ-∘ t)
  renⁿᶠ-∘ (ƛⁿᶠ  b) = cong ƛⁿᶠ_ (renⁿᶠ-∘ b)

renˢᵉᵐ-∘ : ∀ {σ Γ Δ Θ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (x : ⟦ σ ⟧ᵀ Γ)
         -> renˢᵉᵐ (κ ∘ˢ ι) x ≡ renˢᵉᵐ κ (renˢᵉᵐ ι x)
renˢᵉᵐ-∘ {⋆    } t = renⁿᵉ-∘ t
renˢᵉᵐ-∘ {σ ⇒ τ} f = extᵢ ext λ π -> cong f (sym (assocˢ π _ _))

ren-renˢᵉᵐ : ∀ {σ Γ Δ} {ι : Γ ⊆ Δ} (v : σ ∈ Γ)
           -> ↑ (varⁿᵉ (ren ι v)) ≡ renˢᵉᵐ ι (↑ (varⁿᵉ v))
ren-renˢᵉᵐ {⋆    } v = refl
ren-renˢᵉᵐ {σ ⇒ τ} v = extᵢ ext λ κ -> ext λ x -> cong (λ f -> ↑ (varⁿᵉ f ·ⁿᵉ ↓ x))
                                                       (sym (ren-∘ κ _ v))

▷-ren : ∀ {Γ Δ Θ Ξ σ τ} {κ : Θ ⊆ Ξ} {ι : Γ ⊆ Δ} {ρ : Δ ↦ Θ} (x : ⟦ σ ⟧ᵀ Ξ) (v : τ ∈ Γ ▻ σ)
      -> (renˢᵉᵐ κ ∘ ρ ∘ ren ι ▷ x) v ≡ (renˢᵉᵐ κ ∘ ρ ▷ x) (ren (keep ι) v)
▷-ren x  vz    = refl
▷-ren x (vs v) = refl

⟦⟧-ren-sub : ∀ {Γ Δ Θ σ} {ι : Γ ⊆ Δ} {ρ : Δ ↦ Θ} (t : Γ ⊢ σ)
           -> ⟦ t ⟧ (ρ ∘ ren ι) ≡ ⟦ sub ι t ⟧ ρ
⟦⟧-ren-sub             (var v) = refl
⟦⟧-ren-sub             (ƛ b  ) = extᵢ ext λ κ -> ext λ x -> trans (cong ⟦ b ⟧ (extᵢ ext ▷-ren x))
                                                                  (⟦⟧-ren-sub b)
⟦⟧-ren-sub {ι = ι} {ρ} (f · x) rewrite ⟦⟧-ren-sub {ι = ι} {ρ} f
                               |       ⟦⟧-ren-sub {ι = ι} {ρ} x
                               = refl

⟦⟧-resp-≈ : ∀ {Γ Δ σ} {ρ χ : Γ ↦ Δ} (t : Γ ⊢ σ)
          -> (∀ {σ} (v : σ ∈ Γ) -> ρ v ≡ χ v) -> ⟦ t ⟧ ρ ≡ ⟦ t ⟧ χ
⟦⟧-resp-≈ t p = cong ⟦ t ⟧ (extᵢ ext p)
