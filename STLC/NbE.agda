module Categories.STLC.NbE where

open import Function

open import Categories.STLC.STLC

infix  4 _⊢ⁿᵉ_ _⊢ⁿᶠ_ _↦_
infixl 5 _▷_

mutual
  data _⊢ⁿᵉ_ Γ : Type -> Set where
    varⁿᵉ : ∀ {σ}   -> σ ∈ Γ       -> Γ ⊢ⁿᵉ σ
    _·ⁿᵉ_ : ∀ {σ τ} -> Γ ⊢ⁿᵉ σ ⇒ τ -> Γ ⊢ⁿᶠ σ -> Γ ⊢ⁿᵉ τ

  data _⊢ⁿᶠ_ Γ : Type -> Set where
    neⁿᶠ : ∀ {σ}   -> Γ ⊢ⁿᵉ σ     -> Γ ⊢ⁿᶠ σ
    ƛⁿᶠ_ : ∀ {σ τ} -> Γ ▻ σ ⊢ⁿᶠ τ -> Γ ⊢ⁿᶠ σ ⇒ τ

mutual
  embⁿᵉ : ∀ {Γ σ} -> Γ ⊢ⁿᵉ σ -> Γ ⊢ σ
  embⁿᵉ (varⁿᵉ v) = var v
  embⁿᵉ (f ·ⁿᵉ x) = embⁿᵉ f · embⁿᶠ x

  embⁿᶠ : ∀ {Γ σ} -> Γ ⊢ⁿᶠ σ -> Γ ⊢ σ
  embⁿᶠ (neⁿᶠ n) = embⁿᵉ n
  embⁿᶠ (ƛⁿᶠ  b) = ƛ (embⁿᶠ b)

mutual
  renⁿᵉ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᵉ σ -> Δ ⊢ⁿᵉ σ
  renⁿᵉ ι (varⁿᵉ v) = varⁿᵉ (ren ι v)
  renⁿᵉ ι (f ·ⁿᵉ x) = renⁿᵉ ι f ·ⁿᵉ renⁿᶠ ι x

  renⁿᶠ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ⁿᶠ σ -> Δ ⊢ⁿᶠ σ
  renⁿᶠ ι (neⁿᶠ n) = neⁿᶠ (renⁿᵉ ι n)
  renⁿᶠ ι (ƛⁿᶠ  b) = ƛⁿᶠ  (renⁿᶠ (keep ι) b)

⟦_⟧ᵀ : Type -> Con -> Set
⟦ ⋆     ⟧ᵀ Γ = Γ ⊢ⁿᵉ ⋆
⟦ σ ⇒ τ ⟧ᵀ Γ = ∀ {Δ} -> Γ ⊆ Δ -> ⟦ σ ⟧ᵀ Δ -> ⟦ τ ⟧ᵀ Δ

renˢᵉᵐ : ∀ {σ Γ Δ} -> Γ ⊆ Δ -> ⟦ σ ⟧ᵀ Γ -> ⟦ σ ⟧ᵀ Δ
renˢᵉᵐ {⋆    } ι t = renⁿᵉ ι t
renˢᵉᵐ {σ ⇒ τ} ι f = λ κ x -> f (κ ∘ˢ ι) x

mutual
  ↑ : ∀ {σ Γ} -> Γ ⊢ⁿᵉ σ -> ⟦ σ ⟧ᵀ Γ
  ↑ {⋆    } t = t
  ↑ {σ ⇒ τ} f = λ ι x -> ↑ (renⁿᵉ ι f ·ⁿᵉ ↓ x)

  ↓ : ∀ {σ Γ} -> ⟦ σ ⟧ᵀ Γ -> Γ ⊢ⁿᶠ σ
  ↓ {⋆    } t = neⁿᶠ t
  ↓ {σ ⇒ τ} f = ƛⁿᶠ (↓ (f topˢ (varˢᵉᵐ vz)))

  varˢᵉᵐ : ∀ {Γ σ} -> σ ∈ Γ -> ⟦ σ ⟧ᵀ Γ
  varˢᵉᵐ v = ↑ (varⁿᵉ v)

_↦_ : Con -> Con -> Set
Γ ↦ Δ = ∀ {σ} -> σ ∈ Γ -> ⟦ σ ⟧ᵀ Δ

_▷_ : ∀ {Γ Δ σ} -> Γ ↦ Δ -> ⟦ σ ⟧ᵀ Δ -> Γ ▻ σ ↦ Δ
(ρ ▷ x)  vz    = x
(ρ ▷ x) (vs v) = ρ v

⟦_⟧ : ∀ {Γ Δ σ} -> Γ ⊢ σ -> Γ ↦ Δ -> ⟦ σ ⟧ᵀ Δ
⟦ var v ⟧ ρ = ρ v
⟦ ƛ b   ⟧ ρ = λ ι x -> ⟦ b ⟧ (renˢᵉᵐ ι ∘ ρ ▷ x)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ idˢ (⟦ x ⟧ ρ)

norm : ∀ {Γ σ} -> Γ ⊢ σ -> Γ ⊢ σ
norm x = embⁿᶠ (↓ (⟦ x ⟧ varˢᵉᵐ))
