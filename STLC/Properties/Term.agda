module Categories.STLC.Properties.Term where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core

renᵛ-idˢ : ∀ {Γ σ} (v : σ ∈ Γ) -> renᵛ idˢ v ≡ v
renᵛ-idˢ  vz    = refl
renᵛ-idˢ (vs v) = cong vs (renᵛ-idˢ v)

renᵛ-∘ : ∀ {Γ Δ Θ σ} (κ : Δ ⊆ Θ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ) -> renᵛ (κ ∘ˢ ι) v ≡ renᵛ κ (renᵛ ι v)
renᵛ-∘  stop     stop     ()
renᵛ-∘ (skip κ)  ι        v     = cong vs (renᵛ-∘ κ ι v)
renᵛ-∘ (keep κ) (skip ι)  v     = cong vs (renᵛ-∘ κ ι v)
renᵛ-∘ (keep κ) (keep ι)  vz    = refl
renᵛ-∘ (keep κ) (keep ι) (vs v) = cong vs (renᵛ-∘ κ ι v)

ren-idˢ : ∀ {Γ σ} (t : Γ ⊢ σ) -> ren idˢ t ≡ t
ren-idˢ (var v) = cong var (renᵛ-idˢ v)
ren-idˢ (ƛ b  ) = cong ƛ (ren-idˢ b)
ren-idˢ (f · x) = cong₂ _·_ (ren-idˢ f) (ren-idˢ x)

ren-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ σ) -> ren (κ ∘ˢ ι) t ≡ ren κ (ren ι t)
ren-∘ {κ = κ} (var v) = cong var (renᵛ-∘ κ _ v)
ren-∘         (ƛ b  ) = cong ƛ (ren-∘ b)
ren-∘         (f · x) = cong₂ _·_ (ren-∘ f) (ren-∘ x)
