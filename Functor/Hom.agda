module Categories.Functor.Hom where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Agda

Hom[_][-,-] : ∀ {α β γ} -> (C : Category α β γ) -> Profunctor C C
Hom[ C ][-,-] = record
  { F·       = λ o -> record
      { carrier = uncurry _⇒_ o
      ; struct  = inst o
      }
  ; F⇒       = λ o -> record
      { ⟨_⟩       = Hom[ o ]
      ; ⟨⟩-resp-≈ = ∘-resp-≈ʳˡ
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
          (g₂ ∘  g₁) ∘  h₁ ∘ f₂  ∘ f₁ →⟨ ∘-resp-≈ʳˡ r    ⟩
          (g₂ ∘  g₁) ∘  h₂ ∘ f₂  ∘ f₁ ←⟨ ∘-resp-≈ˡ assoc ⟩
          (g₂ ∘  g₁) ∘ (h₂ ∘ f₂) ∘ f₁ →⟨ assoc           ⟩
           g₂ ∘  g₁  ∘ (h₂ ∘ f₂) ∘ f₁ ←⟨ ∘-resp-≈ˡ assoc ⟩
           g₂ ∘ (g₁  ∘  h₂ ∘ f₂) ∘ f₁
        ∎

      F-resp-≈ : ∀ {A B C D} {f₂ f₁ : C ⇒ A} {g₂ g₁ : B ⇒ D} {h₁ h₂ : A ⇒ B}
               -> f₁ ≈ f₂ ×ₚ g₁ ≈ g₂ -> h₁ ≈ h₂ -> Hom[ f₁ , g₁ ] h₁ ≈ Hom[ f₂ , g₂ ] h₂
      F-resp-≈ (p , q) r = ∘-resp-≈ q (∘-resp-≈ r p)

module _ {α β γ} {C : Category α β γ} where
  open IEqReasoningWith C

  Hom[_,-] : Obj -> Copresheaf C
  Hom[ A ,-] = reduceˡ Hom[ C ][-,-] (constᶠ {C₂ = C ᵒᵖ} A)

  Hom[-,_] : Obj -> Presheaf   C
  Hom[-, B ] = reduceʳ Hom[ C ][-,-] (constᶠ {C₂ = C   } B)

  Hom-NaturalTransformation₁ : ∀ {A₁ A₂} -> A₂ ⇒ A₁ -> NaturalTransformation Hom[ A₁ ,-] Hom[ A₂ ,-]
  Hom-NaturalTransformation₁ f = record
    { η          = record
        { ⟨_⟩       = λ g -> g ∘ f
        ; ⟨⟩-resp-≈ = ∘-resp-≈ʳ
        }
    ; naturality = λ {_ _ h g₁ g₂} q ->
        begin
          (h ∘ g₁ ∘ id) ∘ f   ←⟨ ∘-resp-≈ʳ assoc ⟩
          ((h ∘ g₁) ∘ id) ∘ f →⟨ ∘-resp-≈ʳ idʳ   ⟩
          (h ∘ g₁) ∘ f        →⟨ ∘-resp-≈ˡʳ q    ⟩
          (h ∘ g₂) ∘ f        →⟨ assoc           ⟩
          h ∘ g₂ ∘ f          ←⟨ idʳ             ⟩
          (h ∘ g₂ ∘ f) ∘ id   →⟨ assoc           ⟩
          h ∘ (g₂ ∘ f) ∘ id
        ∎
    }

  Hom-NaturalTransformation₂ : ∀ {B₁ B₂} -> B₁ ⇒ B₂ -> NaturalTransformation Hom[-, B₁ ] Hom[-, B₂ ]
  Hom-NaturalTransformation₂ g = record
    { η          = record
        { ⟨_⟩       = λ f -> g ∘ f
        ; ⟨⟩-resp-≈ = ∘-resp-≈ˡ
        }
    ; naturality = λ {_ _ h f₁ f₂} p ->
        begin
          g ∘ id ∘ f₁ ∘ h   →⟨ ∘-resp-≈ˡ idˡ ⟩
          g ∘ f₁ ∘ h        →⟨ ∘-resp-≈ʳˡ p  ⟩
          g ∘ f₂ ∘ h        ←⟨ assoc         ⟩
          (g ∘ f₂) ∘ h      ←⟨ idˡ           ⟩
          id ∘ (g ∘ f₂) ∘ h
        ∎
    }
