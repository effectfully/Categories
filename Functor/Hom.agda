module Categories.Functor.Hom where

open import Relation.Binary.PropositionalEquality as PE hiding (refl)

open import Data.Product

open import Categories.Category.Base
open import Categories.Functor.Base
open import Categories.Categories.Agda

Hom[-,-] : ∀ {α β γ} {C : Category α β γ} -> Bifunctor (C ᵒᵖ) C Agda
Hom[-,-] {C = C} = record
  { F·       = uncurry _⇒_
  ; F⇒       = Hom[_]
  ; F-id     = λ   h -> really  F-id
  ; F-∘      = λ   h -> really  F-∘
  ; F-resp-≈ = λ p h -> really (F-resp-≈ p)
  } where
      open IEqReasoningWith C
      postulate really : ∀ {A B} {f g : A ⇒ B} -> f ≈ g -> f ≡ g

      Hom[_] : ∀ {A B C D} -> C ⇒ A × B ⇒ D -> A ⇒ B -> C ⇒ D
      Hom[ f , g ] h = g ∘ h ∘ f

      F-id : ∀ {A B} {h : A ⇒ B} -> Hom[ id , id ] h ≈ h
      F-id = idˡ ⋯ idʳ

      F-∘ : ∀ {A B₁ B₂ C₁ C₂ D} {f₂ : C₂ ⇒ A} {f₁ : C₁ ⇒ C₂}
              {g₂ : B₂ ⇒ D} {g₁ : B₁ ⇒ B₂} {h : A ⇒ B₁}
          -> Hom[ f₂ ∘ f₁ , g₂ ∘ g₁ ] h ≈ Hom[ f₁ , g₂ ] (Hom[ f₂ , g₁ ] h)
      F-∘ {D = D} {f₂} {f₁} {g₂} {g₁} {h} =
        begin
          (g₂ ∘  g₁) ∘  h ∘ f₂  ∘ f₁ ←⟨ ∘-resp-≈ˡ assoc ⟩
          (g₂ ∘  g₁) ∘ (h ∘ f₂) ∘ f₁ →⟨ assoc           ⟩
           g₂ ∘  g₁  ∘ (h ∘ f₂) ∘ f₁ ←⟨ ∘-resp-≈ˡ assoc ⟩
           g₂ ∘ (g₁  ∘  h ∘ f₂) ∘ f₁
        ∎

      F-resp-≈ : ∀ {A B C D} {f₂ f₁ : C ⇒ A} {g₂ g₁ : B ⇒ D} {h : A ⇒ B}
               -> f₁ ≈ f₂ × g₁ ≈ g₂ -> Hom[ f₁ , g₁ ] h ≈ Hom[ f₂ , g₂ ] h
      F-resp-≈ (p₁ , p₂) = ∘-resp-≈ p₂ (∘-resp-≈ˡ p₁)
