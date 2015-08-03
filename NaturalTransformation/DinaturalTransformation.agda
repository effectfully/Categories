module Categories.NaturalTransformation.DinaturalTransformation where

open import Categories.Category
open import Categories.Functor

record DinaturalTransformation {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                               (F₁ F₂ : Bifunctor (C₁ ᵒᵖ) C₁ C₂) : Set (α₁ ⊔ β₁ ⊔ β₂ ⊔ γ₂) where
  open Category₁ C₁; open Category₂ C₂
  open Functor₁ (bifunctor F₁); open Functor₂ (bifunctor F₂)

  field
--     α : ∀ {A} -> F·₁ (A , A) ⇒₂ F·₂ (A , A)

--     dinaturality : ∀ {A B} {f : A ⇒₁ B}
--                  -> F⇒₂ (id₁ , f) ∘₂ α ∘₂ F⇒₁ (f , id₁) ≈₂ F⇒₂ (f , id₁) ∘₂ α ∘₂ F⇒₁ (id₁ , f)

    α : ∀ {A B} -> F·₁ (A , B) ⇒₂ F·₂ (A , B)

    dinaturality : ∀ {A₁ A₂ B₁ B₂} {f₁ : A₁ ⇒₁ B₁} {f₂ : A₂ ⇒₁ B₂}
                 -> F⇒₂ (id₁ , f₂) ∘₂ α ∘₂ F⇒₁ (f₁ , id₁) ≈₂ F⇒₂ (f₁ , id₁) ∘₂ α ∘₂ F⇒₁ (id₁ , f₂)

idᵈ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
    -> (F : Bifunctor (C₁ ᵒᵖ) C₁ C₂) -> DinaturalTransformation F F
idᵈ {C₁ = C₁} {C₂ = C₂} F = record
  { α            = id₂
  ; dinaturality = λ {_ _ _ _ f₁ f₂} ->
      begin
        F⇒ (id₁ , f₂) ∘₂ id₂ ∘₂ F⇒ (f₁ , id₁) →⟨ ∘-resp-≈ˡ idˡ₂         ⟩
        F⇒ (id₁ , f₂) ∘₂ F⇒ (f₁ , id₁)        ←⟨ F-∘                    ⟩
        F⇒ (f₁ ∘₁ id₁ , f₂ ∘₁ id₁)            →⟨ F-resp-≈ (idʳ₁ , idʳ₁) ⟩
        F⇒ (f₁ , f₂)                          ←⟨ F-resp-≈ (idˡ₁ , idˡ₁) ⟩
        F⇒ (id₁ ∘₁ f₁ , id₁ ∘₁ f₂)            →⟨ F-∘                    ⟩
        F⇒ (f₁ , id₁) ∘₂ F⇒ (id₁ , f₂)        ←⟨ ∘-resp-≈ˡ idˡ₂         ⟩
        F⇒ (f₁ , id₁) ∘₂ id₂ ∘₂ F⇒ (id₁ , f₂)
      ∎
  } where open Functor (bifunctor F); open Category₁ C₁; open Category₂ C₂
          open IEqReasoningFrom C₂; open Tools₂
