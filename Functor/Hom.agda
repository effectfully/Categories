module Categories.Functor.Hom where

open import Categories.Category
open import Categories.Functor
open import Categories.Categories.Agda

Hom[-,-] : ∀ {α β γ} {C : Category α β γ} -> Bifunctor (C ᵒᵖ) C Setoids 
Hom[-,-] {C = C} = record
  { F·       = λ o -> record
      { carrier = uncurry _⇒_ o
      ; struct  = inst o
      }
  ; F⇒       = λ o -> record
      { ⟨_⟩       = Hom[ o ]
      ; ⟨⟩-resp-≈ = ∘-resp-≈²
      }
  ; F-id     = F-id
  ; F-∘      = F-∘
  ; F-resp-≈ = λ p r -> F-resp-≈ p r
  } where
      open IEqReasoningWith C

      Hom[_] : ∀ {A B C D} -> C ⇒ A ×ₚ B ⇒ D -> A ⇒ B -> C ⇒ D
      Hom[ f , g ] h = g ∘ h ∘ f

      F-id : ∀ {A B} {h₁ h₂ : A ⇒ B} -> h₁ ≈ h₂ -> Hom[ id , id ] h₁ ≈ h₂
      F-id r = idˡ ⋯ idʳ ⋯ r

      F-∘ : ∀ {A B₁ B₂ C₁ C₂ D} {f₂ : C₂ ⇒ A} {f₁ : C₁ ⇒ C₂}
              {g₂ : B₂ ⇒ D} {g₁ : B₁ ⇒ B₂} {h₁ h₂ : A ⇒ B₁}
          -> h₁ ≈ h₂ -> Hom[ f₂ ∘ f₁ , g₂ ∘ g₁ ] h₁ ≈ Hom[ f₁ , g₂ ] (Hom[ f₂ , g₁ ] h₂)
      F-∘ {D = D} {f₂} {f₁} {g₂} {g₁} {h₁} {h₂} r =
        begin
          (g₂ ∘  g₁) ∘  h₁ ∘ f₂  ∘ f₁ →⟨ ∘-resp-≈² r     ⟩
          (g₂ ∘  g₁) ∘  h₂ ∘ f₂  ∘ f₁ ←⟨ ∘-resp-≈ˡ assoc ⟩
          (g₂ ∘  g₁) ∘ (h₂ ∘ f₂) ∘ f₁ →⟨ assoc           ⟩
           g₂ ∘  g₁  ∘ (h₂ ∘ f₂) ∘ f₁ ←⟨ ∘-resp-≈ˡ assoc ⟩
           g₂ ∘ (g₁  ∘  h₂ ∘ f₂) ∘ f₁
        ∎

      F-resp-≈ : ∀ {A B C D} {f₂ f₁ : C ⇒ A} {g₂ g₁ : B ⇒ D} {h₁ h₂ : A ⇒ B}
               -> f₁ ≈ f₂ ×ₚ g₁ ≈ g₂ -> h₁ ≈ h₂ -> Hom[ f₁ , g₁ ] h₁ ≈ Hom[ f₂ , g₂ ] h₂
      F-resp-≈ (p , q) r = ∘-resp-≈ q (∘-resp-≈ r p)
