module Categories.STLC.Properties.Eval where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core
open import Categories.STLC.Core.Eval
open import Categories.STLC.Ext

▷-ren : ∀ {Γ Δ σ τ} {ι : Γ ⊆ Δ} {ρ : Env Δ} (x : ⟦ σ ⟧ᵀ) (v : τ ∈ Γ ▻ σ)
      -> (ρ ∘ ren ι ▷ x) v ≡ (ρ ▷ x) (ren (keep ι) v)
▷-ren x  vz    = refl
▷-ren x (vs v) = refl

⟦⟧-ren-sub : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {ρ : Env Δ} (t : Γ ⊢ σ)
           -> ⟦ t ⟧ (ρ ∘ ren ι) ≡ ⟦ sub ι t ⟧ ρ
⟦⟧-ren-sub             (var v) = refl
⟦⟧-ren-sub             (ƛ b  ) = ext λ x -> trans (cong ⟦ b ⟧ (extᵢ ext ▷-ren x))
                                                  (⟦⟧-ren-sub b)
⟦⟧-ren-sub {ι = ι} {ρ} (f · x) rewrite ⟦⟧-ren-sub {ι = ι} {ρ} f
                               |       ⟦⟧-ren-sub {ι = ι} {ρ} x
                               = refl

⟦⟧-resp-≈ : ∀ {Γ σ} {ρ χ : Env Γ} (t : Γ ⊢ σ)
          -> (∀ {σ} (v : σ ∈ Γ) -> ρ v ≡ χ v) -> ⟦ t ⟧ ρ ≡ ⟦ t ⟧ χ
⟦⟧-resp-≈ t p = cong ⟦ t ⟧ (extᵢ ext p)
