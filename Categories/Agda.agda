module Categories.Categories.Agda where

open import Categories.Utilities.Prelude
open import Categories.Utilities.Product
open import Categories.Category

Sets : ∀ {α} -> Category (suc α) α α
Sets {α} = record
  { Obj      = Set α
  ; _⇒_      = λ A B -> A -> B
  ; setoid   = →-ISetoid₂
  ; id       = id′
  ; _∘_      = λ g f -> g ∘′ f
  ; idˡ      = λ _ -> prefl
  ; idʳ      = λ _ -> prefl
  ; assoc    = λ _ -> prefl
  ; ∘-resp-≈ = ∘′-resp-≡
  } where
      ∘′-resp-≡ : ∀ {α} {A B C : Set α} {g₁ g₂ : B -> C} {f₁ f₂ : A -> B}
                -> (∀ y -> g₁ y ≡ g₂ y) -> (∀ x -> f₁ x ≡ f₂ x) -> ∀ x -> g₁ (f₁ x) ≡ g₂ (f₂ x)
      ∘′-resp-≡ q p x rewrite p x = q _

module _ {α} where
  open import Categories.Universal.Limit.Product   (Sets {α})
  open import Categories.Universal.Limit.Equalizer (Sets {α})
  open import Categories.Universal.Limit.Pullback  (Sets {α})
  open import Categories.Universal.Limit.Relations (Sets {α})

  binaryProducts : BinaryProducts
  binaryProducts {A} {B} = record
    { Ob        = A ×ₚ B
    ; π¹        = proj₁
    ; π²        = proj₂
    ; _↑_       = <_,_>
    ; ↑-inj     = λ p -> proj₁ ∘′ ,′-inj ∘′ p , proj₂ ∘′ ,′-inj ∘′ p
    ; universal = λ p q x -> cong₂ _,_ (psym (p x)) (psym (q x))
    }

  equalizers : Equalizers
  equalizers {f = f} {g = g} = record
    { Ob        = ∃ᵢ λ x -> f x ≡ g x
    ; ι         = iproj₁
    ; ↙_⟨_⟩     = λ p r x -> p x ,ᵢ r x
    ; comm      = iproj₂
    ; ↙-inj     = λ p x -> ,ᵢ-inj₁ (p x)
    ; universal = λ r x -> ∃ᵢ-η (r x)
    }

  pullbacks : Pullbacks
  pullbacks = Product&Equalizer->Pullback binaryProducts equalizers

Setoids : ∀ {α γ} -> Category (suc (α ⊔ γ)) (α ⊔ γ) (α ⊔ γ)
Setoids {α} {γ} = record
  { Obj      = Setoid A γ , A ∈ Set α
  ; _⇒_      = λ s₁ s₂ -> struct s₁ ─> struct s₂
  ; setoid   = ─>-ISetoid₂
  ; id       = idˢ
  ; _∘_      = _∘ˢ_
  ; idˡ      = λ {Aˢ Bˢ f}           r -> ⟨⟩-resp-≈ f r
  ; idʳ      = λ {Aˢ Bˢ f}           r -> ⟨⟩-resp-≈ f r
  ; assoc    = λ {Aˢ Bˢ Cˢ Dˢ h g f} r -> ⟨⟩-resp-≈ (h ∘ˢ g ∘ˢ f) r
  ; ∘-resp-≈ = λ q p r -> q (p r)
  } where open Π
