module Categories.STLC.Properties.Eval where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core
open import Categories.STLC.Core.Eval
open import Categories.STLC.Ext

▷-renᵛ : ∀ {Γ Δ σ τ} {ι : Γ ⊆ Δ} {ρ : Env Δ} (x : ⟦ σ ⟧ᵀ) (v : τ ∈ Γ ▻ σ)
      -> (ρ ∘ renᵛ ι ▷ x) v ≡ (ρ ▷ x) (renᵛ (keep ι) v)
▷-renᵛ x  vz    = refl
▷-renᵛ x (vs v) = refl

⟦⟧-renᵛ-ren : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {ρ : Env Δ} (t : Γ ⊢ σ)
           -> ⟦ t ⟧ (ρ ∘ renᵛ ι) ≡ ⟦ ren ι t ⟧ ρ
⟦⟧-renᵛ-ren             (var v) = refl
⟦⟧-renᵛ-ren             (ƛ b  ) = ext λ x -> trans (cong ⟦ b ⟧ (extᵢ ext ▷-renᵛ x))
                                                  (⟦⟧-renᵛ-ren b)
⟦⟧-renᵛ-ren {ι = ι} {ρ} (f · x) rewrite ⟦⟧-renᵛ-ren {ι = ι} {ρ} f
                               |       ⟦⟧-renᵛ-ren {ι = ι} {ρ} x
                               = refl

⟦⟧-resp-≈ : ∀ {Γ σ} {ρ χ : Env Γ} (t : Γ ⊢ σ)
          -> (∀ {σ} (v : σ ∈ Γ) -> ρ v ≡ χ v) -> ⟦ t ⟧ ρ ≡ ⟦ t ⟧ χ
⟦⟧-resp-≈ t p = cong ⟦ t ⟧ (extᵢ ext p)
