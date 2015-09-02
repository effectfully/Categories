module Categories.NaturalTransformation.Lambda where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.OPE
open import Categories.Categories.Agda

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

ren : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
ren  stop     ()
ren (skip ι)  v     = vs (ren ι v)
ren (keep ι)  vz    = vz
ren (keep ι) (vs v) = vs (ren ι v)

sub : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ σ
sub ι (var v) = var (ren ι v)
sub ι (ƛ b  ) = ƛ (sub (keep ι) b)
sub ι (f · x) = sub ι f · sub ι x

ren-idˢ : ∀ {Γ σ} (v : σ ∈ Γ) -> ren idˢ v ≡ v
ren-idˢ  vz    = prefl
ren-idˢ (vs v) = cong vs (ren-idˢ v)

ren-∘ : ∀ {Γ Δ Θ σ} (κ : Δ ⊆ Θ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ) -> ren (κ ∘ˢ ι) v ≡ ren κ (ren ι v)
ren-∘  stop     stop     ()
ren-∘ (skip κ)  ι        v     = cong vs (ren-∘ κ ι v)
ren-∘ (keep κ) (skip ι)  v     = cong vs (ren-∘ κ ι v)
ren-∘ (keep κ) (keep ι)  vz    = prefl
ren-∘ (keep κ) (keep ι) (vs v) = cong vs (ren-∘ κ ι v)

sub-idˢ : ∀ {Γ σ} (t : Γ ⊢ σ) -> sub idˢ t ≡ t
sub-idˢ (var v) = cong var (ren-idˢ v)
sub-idˢ (ƛ b  ) = cong ƛ (sub-idˢ b)
sub-idˢ (f · x) = cong₂ _·_ (sub-idˢ f) (sub-idˢ x)

sub-∘ : ∀ {Γ Δ Θ σ} {κ : Δ ⊆ Θ} {ι : Γ ⊆ Δ} (t : Γ ⊢ σ) -> sub (κ ∘ˢ ι) t ≡ sub κ (sub ι t)
sub-∘ {κ = κ} {ι} (var v) = cong var (ren-∘ κ ι v)
sub-∘             (ƛ b  ) = cong ƛ (sub-∘ b)
sub-∘             (f · x) = cong₂ _·_ (sub-∘ f) (sub-∘ x)

Ren : Functor (OPE Type) (ISets Type)
Ren = record
  { F·       = flip _∈_
  ; F⇒       = λ ι v -> ren ι v
  ; F-id     = ren-idˢ
  ; F-∘      = λ {_ _ _ κ ι} -> ren-∘ κ ι
  ; F-resp-≈ = λ p v -> cong (flip ren v) p
  }

Sub : Functor (OPE Type) (ISets Type)
Sub = record
  { F·       = _⊢_
  ; F⇒       = λ ι t -> sub ι t
  ; F-id     = sub-idˢ
  ; F-∘      = sub-∘
  ; F-resp-≈ = λ p t -> cong (flip sub t) p
  }

Term : NaturalTransformation Ren Sub
Term = record
  { η          = var
  ; naturality = λ v -> prefl
  }
