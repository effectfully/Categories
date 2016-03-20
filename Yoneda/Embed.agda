module Categories.Yoneda.Embed where

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.NaturalTransformation
open import Categories.Categories.Fun
open import Categories.Categories.Agda

Embed : ∀ {α β γ} {C : Category α β γ} -> Functor C (Presheaves C)
Embed {C = C} = record
  { F·       = Hom[ C ][-,_]
  ; F⇒       = Hom-NaturalTransformation₂ C
  ; F-id     = λ r -> idˡ ⋯ idʳ ⋯ r
  ; F-∘      = λ {_ _ _ g f _ h₁ h₂} r ->
      begin
        (g ∘ f) ∘ h₁ ∘ id        →⟨ ∘-resp-≈ʳˡ r ⟩
        (g ∘ f) ∘ h₂ ∘ id        →⟨ assoc        ⟩
        g ∘ (f ∘ h₂ ∘ id)        ←⟨ idʳ          ⟩
        (g ∘ (f ∘ h₂ ∘ id)) ∘ id →⟨ assoc        ⟩
        g ∘ (f ∘ h₂ ∘ id) ∘ id
      ∎
  ; F-resp-≈ = λ q p -> ∘-resp-≈ q (∘-resp-≈ʳ p)
  } where open IEqReasoningWith C
