module Categories.Categories.Cat where

open import Categories.Category
open import Categories.Functor
open import Categories.Categories.Discrete
open import Categories.Object.Limit.Terminal

1Cat : ∀ {α β γ} -> Category (suc (α ⊔ β ⊔ γ)) (α ⊔ β ⊔ γ) (α ⊔ β ⊔ γ)
1Cat {α} {β} {γ} = record
  { Obj      = Category α β γ
  ; _⇒_      = Functor
  ; setoid   = setoidᶠ
  ; id       = idᶠ
  ; _∘_      = _∘ᶠ_
  ; idˡ      = λ {C₁ C₂}       -> Heterogeneous.hrefl C₂
  ; idʳ      = λ {C₁ C₂}       -> Heterogeneous.hrefl C₂
  ; assoc    = λ {C₁ C₂ C₃ C₄} -> Heterogeneous.hrefl C₄
  ; ∘-resp-≈ = λ {C₁ C₂ C₃ G₁ G₂ F₁ F₂} q p {A B f} ->
      let open Functor; open Heterogeneousᶠ G₂; open MixedEqReasoningFrom C₃ in
        begin
          F⇒ G₁ (F⇒ F₁ f) →⟨ q          ⟩
          F⇒ G₂ (F⇒ F₁ f) →⟨ F-resp-≋ p ⟩
          F⇒ G₂ (F⇒ F₂ f)
        ∎
  }

1Cat-Terminal : Terminal 1Cat
1Cat-Terminal = record
  { Ob        = One
  ; ↝         = record { F⇒ = λ _ -> prefl }
  ; universal = Hetero.hetero _
  }
