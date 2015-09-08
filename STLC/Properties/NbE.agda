module Categories.STLC.Properties.NbE where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core
open import Categories.STLC.Core.NbE
open import Categories.STLC.Properties
open import Categories.STLC.Ext

mutual
  subⁿᵉ-idˢ : ∀ {Γ σ} (t : Γ ⊢ⁿᵉ σ) -> subⁿᵉ idˢ t ≡ t
  subⁿᵉ-idˢ (varⁿᵉ v) = cong varⁿᵉ (ren-idˢ v)
  subⁿᵉ-idˢ (f ·ⁿᵉ x) = cong₂ _·ⁿᵉ_ (subⁿᵉ-idˢ f) (subⁿᶠ-idˢ x)

  subⁿᶠ-idˢ : ∀ {Γ σ} (t : Γ ⊢ⁿᶠ σ) -> subⁿᶠ idˢ t ≡ t
  subⁿᶠ-idˢ (neⁿᶠ t) = cong neⁿᶠ (subⁿᵉ-idˢ t)
  subⁿᶠ-idˢ (ƛⁿᶠ  b) = cong ƛⁿᶠ_ (subⁿᶠ-idˢ b)

subˢᵉᵐ-idˢ : ∀ {σ Γ} (x : ⟦ σ ⟧ᵀ Γ) -> subˢᵉᵐ idˢ x ≡ x
subˢᵉᵐ-idˢ {⋆    } t = subⁿᵉ-idˢ t
subˢᵉᵐ-idˢ {σ ⇒ τ} f = extᵢ ext λ x -> cong f idʳˢ

mutual
  subⁿᵉ-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᵉ σ)
          -> subⁿᵉ (κ ∘ˢ ι) t ≡ subⁿᵉ κ (subⁿᵉ ι t)
  subⁿᵉ-∘ {κ = κ} (varⁿᵉ v) = cong varⁿᵉ (ren-∘ κ _ v)
  subⁿᵉ-∘         (f ·ⁿᵉ x) = cong₂ _·ⁿᵉ_ (subⁿᵉ-∘ f) (subⁿᶠ-∘ x)

  subⁿᶠ-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ⁿᶠ σ)
          -> subⁿᶠ (κ ∘ˢ ι) t ≡ subⁿᶠ κ (subⁿᶠ ι t)
  subⁿᶠ-∘ (neⁿᶠ t) = cong neⁿᶠ (subⁿᵉ-∘ t)
  subⁿᶠ-∘ (ƛⁿᶠ  b) = cong ƛⁿᶠ_ (subⁿᶠ-∘ b)

subˢᵉᵐ-∘ : ∀ {σ Γ Δ Θ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (x : ⟦ σ ⟧ᵀ Γ)
         -> subˢᵉᵐ (κ ∘ˢ ι) x ≡ subˢᵉᵐ κ (subˢᵉᵐ ι x)
subˢᵉᵐ-∘ {⋆    } t = subⁿᵉ-∘ t
subˢᵉᵐ-∘ {σ ⇒ τ} f = extᵢ ext λ π -> cong f (sym (assocˢ π _ _))

ren-subˢᵉᵐ : ∀ {σ Γ Δ} {ι : Γ ⊆ Δ} (v : σ ∈ Γ)
           -> ↑ (varⁿᵉ (ren ι v)) ≡ subˢᵉᵐ ι (↑ (varⁿᵉ v))
ren-subˢᵉᵐ {⋆    } v = refl
ren-subˢᵉᵐ {σ ⇒ τ} v = extᵢ ext λ κ -> ext λ x -> cong (λ f -> ↑ (varⁿᵉ f ·ⁿᵉ ↓ x))
                                                       (sym (ren-∘ κ _ v))

▷-ren : ∀ {Γ Δ Θ Ξ σ τ} {κ : Θ ⊆ Ξ} {ι : Γ ⊆ Δ} {ρ : Δ ↦ Θ} (x : ⟦ σ ⟧ᵀ Ξ) (v : τ ∈ Γ ▻ σ)
      -> (subˢᵉᵐ κ ∘ ρ ∘ ren ι ▷ x) v ≡ (subˢᵉᵐ κ ∘ ρ ▷ x) (ren (keep ι) v)
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
