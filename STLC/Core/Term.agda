module Categories.STLC.Core.Term where

open import Categories.STLC.Core.OPE

infix  4 _∈_ _⊢_
infixr 5 _⇒_

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

-- TODO: rename this stupidness.

ren : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
ren  stop     ()
ren (skip ι)  v     = vs (ren ι v)
ren (keep ι)  vz    = vz
ren (keep ι) (vs v) = vs (ren ι v)

sub : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ σ
sub ι (var v) = var (ren ι v)
sub ι (ƛ b  ) = ƛ (sub (keep ι) b)
sub ι (f · x) = sub ι f · sub ι x
