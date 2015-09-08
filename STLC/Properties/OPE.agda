module Categories.STLC.Properties.OPE where

open import Relation.Binary.PropositionalEquality

open import Categories.STLC.Core.OPE

idˡˢ : ∀ {α} {A : Set α} {Γ Δ : Listʳ A} {ι : Γ ⊆ Δ} -> idˢ ∘ˢ ι ≡ ι
idˡˢ {ι = stop  } = refl
idˡˢ {ι = skip ι} = cong skip idˡˢ
idˡˢ {ι = keep ι} = cong keep idˡˢ

idʳˢ : ∀ {α} {A : Set α} {Γ Δ : Listʳ A} {ι : Γ ⊆ Δ} -> ι ∘ˢ idˢ ≡ ι
idʳˢ {ι = stop  } = refl
idʳˢ {ι = skip ι} = cong skip idʳˢ
idʳˢ {ι = keep ι} = cong keep idʳˢ

assocˢ : ∀ {α} {A : Set α} {Γ₁ Γ₂ Γ₃ Γ₄ : Listʳ A}
           (ι₃ : Γ₃ ⊆ Γ₄) (ι₂ : Γ₂ ⊆ Γ₃) (ι₁ : Γ₁ ⊆ Γ₂)
       -> (ι₃ ∘ˢ ι₂) ∘ˢ ι₁ ≡ ι₃ ∘ˢ (ι₂ ∘ˢ ι₁)
assocˢ  stop      stop      stop     = refl
assocˢ (skip ι₃)  ι₂        ι₁       = cong skip (assocˢ ι₃ ι₂ ι₁)
assocˢ (keep ι₃) (skip ι₂)  ι₁       = cong skip (assocˢ ι₃ ι₂ ι₁)
assocˢ (keep ι₃) (keep ι₂) (skip ι₁) = cong skip (assocˢ ι₃ ι₂ ι₁)
assocˢ (keep ι₃) (keep ι₂) (keep ι₁) = cong keep (assocˢ ι₃ ι₂ ι₁)
