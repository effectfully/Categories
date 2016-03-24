module Categories.STLC.Term where

open import Categories.Category
open import Categories.STLC.OPE

infixr 5 _⇒_
infixr 7 _&_
infix  4 _∈_ _⊢_ _⊢₁_ _⊢*_
infixr 6 _▷_

data Type : Set where
  ⋆   : Type
  _⇒_ : Type -> Type -> Type
  _&_ : Type -> Type -> Type

Con = Listʳ Type

data _∈_ σ : Con -> Set where
  vz : ∀ {Γ} -> σ ∈ Γ ▻ σ
  vs : ∀ {Γ τ} -> σ ∈ Γ -> σ ∈ Γ ▻ τ 

data _⊢_ Γ : Type -> Set where
  var  : ∀ {σ} -> σ ∈ Γ -> Γ ⊢ σ
  ƛ_   : ∀ {σ τ} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ ⇒ τ
  _·_  : ∀ {σ τ} -> Γ ⊢ σ ⇒ τ -> Γ ⊢ σ -> Γ ⊢ τ
  unit : Γ ⊢ ⋆
  pair : ∀ {σ τ} -> Γ ⊢ σ -> Γ ⊢ τ -> Γ ⊢ σ & τ
  fst  : ∀ {σ τ} -> Γ ⊢ σ & τ -> Γ ⊢ σ
  snd  : ∀ {σ τ} -> Γ ⊢ σ & τ -> Γ ⊢ τ

_⊢₁_ : Type -> Type -> Set
σ ⊢₁ τ = ε ▻ σ ⊢ τ

renᵛ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
renᵛ  stop     ()
renᵛ (skip ι)  v     = vs (renᵛ ι v)
renᵛ (keep ι)  vz    = vz
renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

ren : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ⊢ σ -> Δ ⊢ σ
ren ι (var v   ) = var (renᵛ ι v)
ren ι (ƛ b     ) = ƛ (ren (keep ι) b)
ren ι (f · x   ) = ren ι f · ren ι x
ren ι  unit      = unit
ren ι (pair t s) = pair (ren ι t) (ren ι s) 
ren ι (fst p   ) = fst (ren ι p)
ren ι (snd p   ) = snd (ren ι p)

shift : ∀ {Γ σ τ} -> Γ ⊢ σ -> Γ ▻ τ ⊢ σ
shift = ren top

data _⊢*_ Δ : Con -> Set where
  ø   : Δ ⊢* ε
  _▷_ : ∀ {Γ σ} -> Δ ⊢* Γ -> Δ ⊢ σ -> Δ ⊢* Γ ▻ σ

lookup* : ∀ {Δ Γ σ} -> σ ∈ Γ -> Δ ⊢* Γ -> Δ ⊢ σ
lookup*  vz    (ψ ▷ t) = t
lookup* (vs v) (ψ ▷ t) = lookup* v ψ

ren* : ∀ {Δ Ξ Γ} -> Δ ⊆ Ξ -> Δ ⊢* Γ -> Ξ ⊢* Γ
ren* ι  ø      = ø
ren* ι (ψ ▷ t) = ren* ι ψ ▷ ren ι t

shift* : ∀ {Δ Γ τ} -> Δ ⊢* Γ -> Δ ▻ τ ⊢* Γ
shift* = ren* top

keep* : ∀ {Δ Γ σ} -> Δ ⊢* Γ -> Δ ▻ σ ⊢* Γ ▻ σ
keep* ψ = shift* ψ ▷ var vz

id* : ∀ {Γ} -> Γ ⊢* Γ
id* {ε}     = ø
id* {Γ ▻ σ} = keep* id*

sub : ∀ {Δ Γ σ} -> Δ ⊢* Γ -> Γ ⊢ σ -> Δ ⊢ σ
sub ψ (var v   ) = lookup* v ψ
sub ψ (ƛ b     ) = ƛ (sub (keep* ψ) b)
sub ψ (f · x   ) = sub ψ f · sub ψ x
sub ψ  unit      = unit
sub ψ (pair t s) = pair (sub ψ t) (sub ψ s)
sub ψ (fst p   ) = fst (sub ψ p)
sub ψ (snd p   ) = snd (sub ψ p)

_[_]₁ : ∀ {Γ σ τ} -> σ ⊢₁ τ -> Γ ⊢ σ -> Γ ⊢ τ
b [ x ]₁ = sub (ø ▷ x) b

sub* : ∀ {Ξ Δ Γ} -> Ξ ⊢* Δ -> Δ ⊢* Γ -> Ξ ⊢* Γ
sub* φ  ø      = ø
sub* φ (ψ ▷ t) = sub* φ ψ ▷ sub φ t

renᵛ-idˢ : ∀ {Γ σ} (v : σ ∈ Γ) -> renᵛ idˢ v ≡ v
renᵛ-idˢ  vz    = prefl
renᵛ-idˢ (vs v) = cong vs (renᵛ-idˢ v)

renᵛ-∘ : ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (v : σ ∈ Γ) -> renᵛ (κ ∘ˢ ι) v ≡ renᵛ κ (renᵛ ι v)
renᵛ-∘  stop     stop     ()
renᵛ-∘ (skip κ)  ι        v     = cong vs (renᵛ-∘ κ ι v)
renᵛ-∘ (keep κ) (skip ι)  v     = cong vs (renᵛ-∘ κ ι v)
renᵛ-∘ (keep κ) (keep ι)  vz    = prefl
renᵛ-∘ (keep κ) (keep ι) (vs v) = cong vs (renᵛ-∘ κ ι v)

ren-idˢ : ∀ {Γ σ} (t : Γ ⊢ σ) -> ren idˢ t ≡ t
ren-idˢ (var v   ) = cong var (renᵛ-idˢ v)
ren-idˢ (ƛ b     ) = cong ƛ_ (ren-idˢ b)
ren-idˢ (f · x   ) = cong₂ _·_ (ren-idˢ f) (ren-idˢ x)
ren-idˢ  unit      = prefl
ren-idˢ (pair t s) = cong₂ pair (ren-idˢ t) (ren-idˢ s)
ren-idˢ (fst p   ) = cong fst (ren-idˢ p)
ren-idˢ (snd p   ) = cong snd (ren-idˢ p)

ren-∘ : ∀ {Γ Δ Ξ σ} (κ : Δ ⊆ Ξ) (ι : Γ ⊆ Δ) (t : Γ ⊢ σ) -> ren (κ ∘ˢ ι) t ≡ ren κ (ren ι t)
ren-∘ κ ι (var v   ) = cong var (renᵛ-∘ κ ι v)
ren-∘ κ ι (ƛ b     ) = cong ƛ_ (ren-∘ (keep κ) (keep ι) b)
ren-∘ κ ι (f · x   ) = cong₂ _·_ (ren-∘ κ ι f) (ren-∘ κ ι x)
ren-∘ κ ι  unit      = prefl
ren-∘ κ ι (pair t s) = cong₂ pair (ren-∘ κ ι t) (ren-∘ κ ι s)
ren-∘ κ ι (fst p   ) = cong fst (ren-∘ κ ι p)
ren-∘ κ ι (snd p   ) = cong snd (ren-∘ κ ι p)

lookup*-ren* : ∀ {Ξ Δ Γ σ} (v : σ ∈ Γ) (ι : Δ ⊆ Ξ) (ψ : Δ ⊢* Γ)
             -> lookup* v (ren* ι ψ) ≡ ren ι (lookup* v ψ)
lookup*-ren*  vz    ι (ψ ▷ t) = prefl
lookup*-ren* (vs v) ι (ψ ▷ t) = lookup*-ren* v ι ψ

lookup*-id* : ∀ {Γ σ} (v : σ ∈ Γ) -> lookup* v id* ≡ var v
lookup*-id*  vz    = prefl
lookup*-id* (vs v) = ptrans (lookup*-ren* v top id*)
                            (ptrans (cong shift (lookup*-id* v))
                            (cong (var ∘′ vs) (renᵛ-idˢ v)))

sub-id* : ∀ {Γ σ} (t : Γ ⊢ σ) -> sub id* t ≡ t
sub-id* (var v   ) = lookup*-id* v
sub-id* (ƛ b     ) = cong ƛ_ (sub-id* b)
sub-id* (f · x   ) = cong₂ _·_ (sub-id* f) (sub-id* x)
sub-id*  unit      = prefl
sub-id* (pair t s) = cong₂ pair (sub-id* t) (sub-id* s)
sub-id* (fst p   ) = cong fst (sub-id* p)
sub-id* (snd p   ) = cong snd (sub-id* p)

lookup*-sub* : ∀ {Ξ Δ Γ σ} (v : σ ∈ Γ) (φ : Ξ ⊢* Δ) (ψ : Δ ⊢* Γ)
             -> sub φ (lookup* v ψ) ≡ lookup* v (sub* φ ψ)
lookup*-sub*  vz    φ (ψ ▷ t) = prefl
lookup*-sub* (vs v) φ (ψ ▷ t) = lookup*-sub* v φ ψ

postulate
  -- Damn, again.
  sub-shift : ∀ {Δ Γ σ τ} (ψ : Δ ⊢* Γ) (t : Γ ⊢ σ)
            -> sub (keep* {σ = τ} ψ) (shift t) ≡ shift (sub ψ t)
  -- sub (keep*        ψ)  (ren       top  t) ≡ ren       top  (sub        ψ  t)
  -- sub (keep* (keep* ψ)) (ren (keep top) t) ≡ ren (keep top) (sub (keep* ψ) t)

sub*-shift* : ∀ {Ξ Δ Γ σ} (φ : Ξ ⊢* Δ) (ψ : Δ ⊢* Γ)
            -> sub* (keep* {σ = σ} φ) (shift* ψ) ≡ shift* (sub* φ ψ)
sub*-shift* φ  ø      = prefl
sub*-shift* φ (ψ ▷ t) = cong₂ _▷_ (sub*-shift* φ ψ) (sub-shift φ t)

sub-sub : ∀ {Ξ Δ Γ σ} (φ : Ξ ⊢* Δ) (ψ : Δ ⊢* Γ) (t : Γ ⊢ σ) -> sub φ (sub ψ t) ≡ sub (sub* φ ψ) t
sub-sub φ ψ (var v   ) = lookup*-sub* v φ ψ
sub-sub φ ψ (ƛ b     ) = cong ƛ_ (ptrans (sub-sub (keep* φ) (keep* ψ) b)
                                      (cong (λ ρ -> sub (ρ ▷ var vz) b) (sub*-shift* φ ψ)))
sub-sub φ ψ (f · x   ) = cong₂ _·_ (sub-sub φ ψ f) (sub-sub φ ψ x)
sub-sub φ ψ  unit      = prefl
sub-sub φ ψ (pair t s) = cong₂ pair (sub-sub φ ψ t) (sub-sub φ ψ s)
sub-sub φ ψ (fst p   ) = cong fst (sub-sub φ ψ p)
sub-sub φ ψ (snd p   ) = cong snd (sub-sub φ ψ p)
