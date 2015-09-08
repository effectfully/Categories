module Categories.STLC.Core.OPE where

infixl 5 _▻_
infix  4 _⊆_
infixr 9 _∘ˢ_

data Listʳ {α} (A : Set α) : Set α where
  ε   : Listʳ A
  _▻_ : Listʳ A -> A -> Listʳ A

data _⊆_ {α} {A : Set α} : Listʳ A -> Listʳ A -> Set α where
  stop : ε ⊆ ε
  skip : ∀ {Γ Δ x} -> Γ ⊆ Δ -> Γ ⊆ Δ ▻ x
  keep : ∀ {Γ Δ x} -> Γ ⊆ Δ -> Γ ▻ x ⊆ Δ ▻ x

idˢ : ∀ {α} {A : Set α} {Γ : Listʳ A} -> Γ ⊆ Γ
idˢ {Γ = ε    } = stop
idˢ {Γ = Γ ▻ x} = keep idˢ

topˢ : ∀ {α} {A : Set α} {Γ : Listʳ A} {x} -> Γ ⊆ Γ ▻ x
topˢ = skip idˢ

_∘ˢ_ : ∀ {α} {A : Set α} {Γ Δ Θ : Listʳ A} -> Δ ⊆ Θ -> Γ ⊆ Δ -> Γ ⊆ Θ
stop   ∘ˢ stop   = stop
skip ι ∘ˢ κ      = skip (ι ∘ˢ κ)
keep ι ∘ˢ skip κ = skip (ι ∘ˢ κ)
keep ι ∘ˢ keep κ = keep (ι ∘ˢ κ)
