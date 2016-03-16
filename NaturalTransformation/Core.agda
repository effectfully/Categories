module Categories.NaturalTransformation.Core where

open import Categories.Category
open import Categories.Functor

infixr 9 _∘ⁿ_ _∘ʰ_ _∘ˡ_ _∘ʳ_
infix  4 _≈ⁿ_

record NaturalTransformation {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                             (F₁ F₂ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  no-eta-equality

  open Category C₂; open Functor₁ F₁; open Functor₂ F₂ 

  field
    η : ∀ {A} -> F·₁ A ⇒ F·₂ A

    naturality : ∀ {A B} {f : A [ C₁ ]⇒ B} -> η ∘ F⇒₁ f ≈ F⇒₂ f ∘ η

module _ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         {F₁ F₂ : Functor C₁ C₂} (N : NaturalTransformation F₁ F₂) where
  module NaturalTransformation₁ = NaturalTransformation N
    renaming (η to η₁; naturality to naturality₁)

  module NaturalTransformation₂ = NaturalTransformation N
    renaming (η to η₂; naturality to naturality₂)

  module NaturalTransformation₃ = NaturalTransformation N
    renaming (η to η₃; naturality to naturality₃)

idⁿ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {F : Functor C₁ C₂}
    -> NaturalTransformation F F
idⁿ {C₂ = C₂} {F} = record
  { η          = id
  ; naturality = left idˡ idʳ
  } where open Functor F; open Category C₂

_∘ⁿ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         {F₁ : Functor C₁ C₂} {F₂ : Functor C₁ C₂} {F₃ : Functor C₁ C₂}
     -> NaturalTransformation F₂ F₃ -> NaturalTransformation F₁ F₂ -> NaturalTransformation F₁ F₃
_∘ⁿ_ {C₂ = C₂} {F₁} {F₂} {F₃} N₁ N₂ = record
  { η          = λ {A} -> η₁ {A} ∘ η₂ {A}
  ; naturality = λ {A B f} ->
      begin
        (η₁ ∘ η₂) ∘ F⇒₁ f →⟨ ∘²-resp-≈ˡ naturality₂ ⟩
        (η₁ ∘ F⇒₂ f) ∘ η₂ →⟨ ∘ʳ-resp-≈ʳ naturality₁ ⟩
        F⇒₃ f ∘ (η₁ ∘ η₂)
      ∎
  } where open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂
          open Functor₁ F₁; open Functor₂ F₂; open Functor₃ F₃; open IEqReasoningWith C₂

_∘ʰ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
         {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
         {F₁ F₂ : Functor C₁ C₂} {F₃ F₄ : Functor C₂ C₃}
     -> NaturalTransformation F₃ F₄
     -> NaturalTransformation F₁ F₂
     -> NaturalTransformation (F₃ ∘ᶠ F₁) (F₄ ∘ᶠ F₂)
_∘ʰ_ {C₂ = C₂} {C₃ = C₃} {F₁} {F₂} {F₃} {F₄} N₂ N₁ = record
  { η          = F⇒₄ η₁ ∘ η₂
  ; naturality = λ {_ _ f} ->
      begin
        (F⇒₄ η₁ ∘ η₂) ∘ F⇒₃ (F⇒₁ f) ←⟨ ∘-resp-≈ʳ naturality₂             ⟩
        (η₂ ∘ F⇒₃ η₁) ∘ F⇒₃ (F⇒₁ f) →⟨ assoc                             ⟩
        η₂ ∘ (F⇒₃ η₁ ∘ F⇒₃ (F⇒₁ f)) ←⟨ ∘-resp-≈ˡ F-∘₃                    ⟩
        η₂ ∘ F⇒₃ (η₁ ∘₂ F⇒₁ f)      →⟨ naturality₂                       ⟩
        F⇒₄ (η₁ ∘₂ F⇒₁ f) ∘ η₂      →⟨ ∘-resp-≈ʳ (F-resp-≈₄ naturality₁) ⟩
        F⇒₄ (F⇒₂ f ∘₂ η₁) ∘ η₂      →⟨ ∘-resp-≈ʳ F-∘₄                    ⟩
        (F⇒₄ (F⇒₂ f) ∘ F⇒₄ η₁) ∘ η₂ →⟨ assoc                             ⟩
        F⇒₄ (F⇒₂ f) ∘ F⇒₄ η₁ ∘ η₂
      ∎
  } where open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂
          open Functor₁ F₁; open Functor₂ F₂; open Functor₃ F₃; open Functor₄ F₄
          open Category₂ C₂; open IEqReasoningWith C₃

_∘ˡ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
         {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
         {F₁ F₂ : Functor C₁ C₂}
     -> (F₃ : Functor C₂ C₃)
     -> NaturalTransformation F₁ F₂
     -> NaturalTransformation (F₃ ∘ᶠ F₁) (F₃ ∘ᶠ F₂)
F₃ ∘ˡ N = idⁿ {F = F₃} ∘ʰ N

_∘ʳ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
         {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
         {F₂ F₃ : Functor C₂ C₃}
     -> NaturalTransformation F₂ F₃
     -> (F₁ : Functor C₁ C₂)
     -> NaturalTransformation (F₂ ∘ᶠ F₁) (F₃ ∘ᶠ F₁)
N ∘ʳ F₁ = N ∘ʰ idⁿ {F = F₁}

module _ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} where
  open Category C₂

  constⁿ : ∀ {A B} -> A ⇒ B -> NaturalTransformation (constᶠ {C₁ = C₁} A) (constᶠ {C₂ = C₂} B)
  constⁿ f = record
    { η          = f
    ; naturality = left idʳ idˡ
    }

module _ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         (F : Bifunctor (C₁ ᵒᵖ) C₁ C₂)  where
  open Functor (detag F); open Category₁ C₁; open Category₂ C₂; open IEqReasoningFrom C₂

  applyⁿˡ : ∀ {A₁ B₁} -> B₁ ⇒₁ A₁ -> NaturalTransformation (applyᶠˡ F A₁) (applyᶠˡ F B₁)
  applyⁿˡ f₁ = record
    { η          = F⇒ (f₁ , id₁)
    ; naturality = λ {_ _ f₂} ->
        begin
          F⇒ (f₁ , id₁) ∘₂ F⇒ (id₁ , f₂) ←⟨ F-∘                    ⟩
          F⇒ (id₁ ∘₁ f₁ , id₁ ∘₁ f₂)     →⟨ F-resp-≈ (idˡ₁ , idˡ₁) ⟩
          F⇒ (f₁ , f₂)                   ←⟨ F-resp-≈ (idʳ₁ , idʳ₁) ⟩
          F⇒ (f₁ ∘₁ id₁ , f₂ ∘₁ id₁)     →⟨ F-∘                    ⟩
          F⇒ (id₁ , f₂) ∘₂ F⇒ (f₁ , id₁)
        ∎
    }

  applyⁿʳ : ∀ {A₂ B₂} -> A₂ ⇒₁ B₂ -> NaturalTransformation (applyᶠʳ F A₂) (applyᶠʳ F B₂)
  applyⁿʳ f₂ = record
    { η          = F⇒ (id₁ , f₂)
    ; naturality = λ {_ _ f₁} ->
        begin
          F⇒ (id₁ , f₂) ∘₂ F⇒ (f₁ , id₁) ←⟨ F-∘                    ⟩
          F⇒ (f₁ ∘₁ id₁ , f₂ ∘₁ id₁)     →⟨ F-resp-≈ (idʳ₁ , idʳ₁) ⟩
          F⇒ (f₁ , f₂)                   ←⟨ F-resp-≈ (idˡ₁ , idˡ₁) ⟩
          F⇒ (id₁ ∘₁ f₁ , id₁ ∘₁ f₂)     →⟨ F-∘                    ⟩
          F⇒ (f₁ , id₁) ∘₂ F⇒ (id₁ , f₂)
        ∎
    }

setoidⁿ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
        -> ISetoid₂ (NaturalTransformation {C₁ = C₁} {C₂ = C₂}) (α₁ ⊔ γ₂)
setoidⁿ {C₂ = C₂} = comap∀ⁱˢ (λ N A -> let open NaturalTransformation N in η {A}) setoid
  where open Category C₂

_≈ⁿ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         {F₁ : Functor C₁ C₂} {F₂ : Functor C₁ C₂}
     -> NaturalTransformation F₁ F₂ -> NaturalTransformation F₁ F₂ -> Set (α₁ ⊔ γ₂)
_≈ⁿ_ = _≈_
  where open ISetoid setoidⁿ
