module Categories.Functor.Hom where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Agda

Hom[-,-] : ∀ {α β γ} {C : Category α β γ} -> Profunctor C C
Hom[-,-] {C = C} = tag record
  { F·       = hide ∘′ flip instⁱˢ setoid
  ; F⇒       = λ o -> record
      { f·       = Hom[ o ]
      ; f-resp-≈ = ∘-resp-≈ʳˡ
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

Hom[_][-,-] : ∀ {α β γ} -> (C : Category α β γ) -> Profunctor C C
Hom[ _ ][-,-] = Hom[-,-]

module _ {α β γ} {C : Category α β γ} where
  open Category C

  Hom[_,-] : Obj -> Copresheaf C
  Hom[_,-] = applyᶠˡ Hom[-,-]

  Hom-NaturalTransformation₁ : ∀ {A₁ A₂}
                             -> A₂ ⇒ A₁ -> NaturalTransformation Hom[ A₁ ,-] Hom[ A₂ ,-]
  Hom-NaturalTransformation₁ = applyⁿˡ Hom[-,-]

module _ {α β γ} (C : Category α β γ) where
  open Category C

  Hom[_][-,_] : Obj -> Presheaf   C
  Hom[_][-,_] = applyᶠʳ Hom[ C ][-,-]

  Hom-NaturalTransformation₂ : ∀ {B₁ B₂}
                             -> B₁ ⇒ B₂ -> NaturalTransformation (Hom[_][-,_] B₁) (Hom[_][-,_] B₂)
  Hom-NaturalTransformation₂ = applyⁿʳ Hom[ C ][-,-]
