module Categories.STLC.Properties.Term where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core

ren-idˢ : ∀ {Γ σ} (v : σ ∈ Γ) -> ren idˢ v ≡ v
ren-idˢ  vz    = refl
ren-idˢ (vs v) = cong vs (ren-idˢ v)

ren-∘ : ∀ {Γ Δ Θ σ} (κ : Δ ⊆ Θ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ) -> ren (κ ∘ˢ ι) v ≡ ren κ (ren ι v)
ren-∘  stop     stop     ()
ren-∘ (skip κ)  ι        v     = cong vs (ren-∘ κ ι v)
ren-∘ (keep κ) (skip ι)  v     = cong vs (ren-∘ κ ι v)
ren-∘ (keep κ) (keep ι)  vz    = refl
ren-∘ (keep κ) (keep ι) (vs v) = cong vs (ren-∘ κ ι v)

sub-idˢ : ∀ {Γ σ} (t : Γ ⊢ σ) -> sub idˢ t ≡ t
sub-idˢ (var v) = cong var (ren-idˢ v)
sub-idˢ (ƛ b  ) = cong ƛ (sub-idˢ b)
sub-idˢ (f · x) = cong₂ _·_ (sub-idˢ f) (sub-idˢ x)

sub-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ σ) -> sub (κ ∘ˢ ι) t ≡ sub κ (sub ι t)
sub-∘ {κ = κ} (var v) = cong var (ren-∘ κ _ v)
sub-∘         (ƛ b  ) = cong ƛ (sub-∘ b)
sub-∘         (f · x) = cong₂ _·_ (sub-∘ f) (sub-∘ x)
