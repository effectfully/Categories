module Categories.STLC.STLC where

open import Data.Unit

open import Categories.STLC.OPE public

infix  4 _∈_ _⊢_
infixr 5 _⇒_
infixl 5 _▷_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type

Con = Listʳ Type

data _∈_ σ : Con -> Set where
  vz : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ τ} -> σ ∈ Γ     -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var : ∀ {σ}   -> σ ∈ Γ     -> Γ ⊢ σ
  ƛ   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_ : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ     -> Γ ⊢ τ

ren : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
ren  stop     ()
ren (skip ι)  v     = vs (ren ι v)
ren (keep ι)  vz    = vz
ren (keep ι) (vs v) = vs (ren ι v)

sub : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ σ
sub ι (var v) = var (ren ι v)
sub ι (ƛ b  ) = ƛ (sub (keep ι) b)
sub ι (f · x) = sub ι f · sub ι x

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
