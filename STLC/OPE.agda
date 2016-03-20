module Categories.STLC.OPE where

open import Categories.Category

infixl 5 _▻_
infix  4 _⊆_
infixr 9 _∘ˢ_

data Listʳ {α} (A : Set α) : Set α where
  ε   : Listʳ A
  _▻_ : Listʳ A -> A -> Listʳ A

data _⊆_ {α} {A : Set α} : Listʳ A -> Listʳ A -> Set α where
  stop : ε ⊆ ε
  skip : ∀ {Γ Δ x} -> Γ ⊆ Δ -> Γ     ⊆ Δ ▻ x
  keep : ∀ {Γ Δ x} -> Γ ⊆ Δ -> Γ ▻ x ⊆ Δ ▻ x

idˢ : ∀ {α} {A : Set α} {Γ : Listʳ A} -> Γ ⊆ Γ
idˢ {Γ = ε}     = stop
idˢ {Γ = Γ ▻ x} = keep idˢ

top : ∀ {α} {A : Set α} {Γ : Listʳ A} {x} -> Γ ⊆ Γ ▻ x
top = skip idˢ

_∘ˢ_ : ∀ {α} {A : Set α} {Γ Δ Θ : Listʳ A} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢ stop   = stop
skip ι ∘ˢ κ      = skip (ι ∘ˢ κ)
keep ι ∘ˢ skip κ = skip (ι ∘ˢ κ)
keep ι ∘ˢ keep κ = keep (ι ∘ˢ κ)

idˡˢ : ∀ {α} {A : Set α} {Γ Δ : Listʳ A} {ι : Γ ⊆ Δ} -> idˢ ∘ˢ ι ≡ ι
idˡˢ {ι = stop  } = prefl
idˡˢ {ι = skip ι} = cong skip idˡˢ
idˡˢ {ι = keep ι} = cong keep idˡˢ

idʳˢ : ∀ {α} {A : Set α} {Γ Δ : Listʳ A} {ι : Γ ⊆ Δ} -> ι ∘ˢ idˢ ≡ ι
idʳˢ {ι = stop  } = prefl
idʳˢ {ι = skip ι} = cong skip idʳˢ
idʳˢ {ι = keep ι} = cong keep idʳˢ

assocˢ : ∀ {α} {A : Set α} {Γ₁ Γ₂ Γ₃ Γ₄ : Listʳ A}
           (ι₃ : Γ₃ ⊆ Γ₄) (ι₂ : Γ₂ ⊆ Γ₃) (ι₁ : Γ₁ ⊆ Γ₂)
       -> (ι₃ ∘ˢ ι₂) ∘ˢ ι₁ ≡ ι₃ ∘ˢ (ι₂ ∘ˢ ι₁)
assocˢ  stop      stop      stop     = prefl
assocˢ (skip ι₃)  ι₂        ι₁       = cong skip (assocˢ ι₃ ι₂ ι₁)
assocˢ (keep ι₃) (skip ι₂)  ι₁       = cong skip (assocˢ ι₃ ι₂ ι₁)
assocˢ (keep ι₃) (keep ι₂) (skip ι₁) = cong skip (assocˢ ι₃ ι₂ ι₁)
assocˢ (keep ι₃) (keep ι₂) (keep ι₁) = cong keep (assocˢ ι₃ ι₂ ι₁)

OPE : ∀{α} -> Set α -> Category α α α
OPE A = record
  { Obj      = Listʳ A
  ; _⇒_      = _⊆_
  ; setoid   = ≡-ISetoid
  ; id       = idˢ
  ; _∘_      = _∘ˢ_
  ; idˡ      = idˡˢ
  ; idʳ      = idʳˢ
  ; assoc    = λ {_ _ _ _ ι₃ ι₂ ι₁} -> assocˢ ι₃ ι₂ ι₁
  ; ∘-resp-≈ = cong₂ _∘ˢ_
  }
