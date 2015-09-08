module Categories.STLC.Properties where

open import Function
open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Term

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
sub-∘ {κ = κ} {ι} (var v) = cong var (ren-∘ κ ι v)
sub-∘             (ƛ b  ) = cong ƛ (sub-∘ b)
sub-∘             (f · x) = cong₂ _·_ (sub-∘ f) (sub-∘ x)

postulate
  ext  : ∀ {α β} {A : Set α} {B : A -> Set β} {f g : ∀ x -> B x}
       -> (∀ x -> f x ≡ g x) -> f ≡ g
  extᵢ : ∀ {α β} {A : Set α} {B : A -> Set β} {f g : ∀ {x} -> B x}
       -> (∀ {x} -> f {x} ≡ g {x}) -> (λ {x} -> f {x}) ≡ (λ {x} -> g {x})

module Eval where
  open import Categories.STLC.Eval

  ▷-ren : ∀ {Γ Δ σ τ} {ι : Γ ⊆ Δ} {ρ : Env Δ} (x : ⟦ σ ⟧ᵀ) (v : τ ∈ Γ ▻ σ)
        -> (ρ ∘ ren ι ▷ x) v ≡ (ρ ▷ x) (ren (keep ι) v)
  ▷-ren x  vz    = refl
  ▷-ren x (vs v) = refl

  ⟦⟧-ren-sub : ∀ {Γ Δ σ} {ι : Γ ⊆ Δ} {ρ : Env Δ} (t : Γ ⊢ σ)
             -> ⟦ t ⟧ (ρ ∘ ren ι) ≡ ⟦ sub ι t ⟧ ρ
  ⟦⟧-ren-sub             (var v) = refl
  ⟦⟧-ren-sub             (ƛ b  ) = ext (λ x -> trans (cong ⟦ b ⟧ (extᵢ (ext (▷-ren x))))
                                                     (⟦⟧-ren-sub b))
  ⟦⟧-ren-sub {ι = ι} {ρ} (f · x) rewrite ⟦⟧-ren-sub {ι = ι} {ρ} f
                                 |       ⟦⟧-ren-sub {ι = ι} {ρ} x
                                 = refl

module NbE where
  open import Categories.STLC.NbE
