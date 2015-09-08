module Categories.STLC.Core.Eval where

open import Data.Unit

open import Categories.STLC.Core

infixl 5 _▷_

⟦_⟧ᵀ : Type -> Set
⟦ ⋆     ⟧ᵀ = ⊤
⟦ σ ⇒ τ ⟧ᵀ = ⟦ σ ⟧ᵀ -> ⟦ τ ⟧ᵀ

Env : Con -> Set
Env Γ = ∀ {σ} -> σ ∈ Γ -> ⟦ σ ⟧ᵀ

_▷_ : ∀ {Γ σ} -> Env Γ -> ⟦ σ ⟧ᵀ -> Env (Γ ▻ σ)
(ρ ▷ x)  vz    = x
(ρ ▷ x) (vs v) = ρ v

⟦_⟧ : ∀ {Γ σ} -> Γ ⊢ σ -> Env Γ -> ⟦ σ ⟧ᵀ
⟦ var v ⟧ ρ = ρ v
⟦ ƛ b   ⟧ ρ = λ x -> ⟦ b ⟧ (ρ ▷ x)
⟦ f · x ⟧ ρ = ⟦ f ⟧ ρ (⟦ x ⟧ ρ)
