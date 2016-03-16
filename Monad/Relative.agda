module Categories.Monad.Relative where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Monad.Core

-- class (Functor j) => RelativeMonad j t where
--   return :: j a -> t a
--   (>>=)  :: t a -> (j a -> t b) -> t b

record RelativeMonad {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                     (J : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open Category₁ C₁; open IEqReasoningWith C₂
  open Functor J renaming (F· to ⟨_⟩₀; F⇒ to fmap₀;
                           F-∘ to fmap₀-∘; F-id to fmap₀-id; F-resp-≈ to fmap₀-resp-≈) public

  infix  2 >>=_
  infixr 2 _<=<_ _>=>_

  field
    ⟨_⟩  : Obj₁ -> Obj
    pure : ∀ {A} -> ⟨ A ⟩₀ ⇒ ⟨ A ⟩
    >>=_ : ∀ {A B} -> ⟨ A ⟩₀ ⇒ ⟨ B ⟩ -> ⟨ A ⟩ ⇒ ⟨ B ⟩

    >>=-pure   : ∀ {A} -> (>>= pure) ≈ id {⟨ A ⟩}
    pure->=>   : ∀ {A B} {f : ⟨ A ⟩₀ ⇒ ⟨ B ⟩} -> (>>= f) ∘ pure ≈ f
    >>=->>=    : ∀ {A B} {f : ⟨ A ⟩₀ ⇒ ⟨ B ⟩} {g : ⟨ B ⟩₀ ⇒ ⟨ A ⟩}
               -> (>>= (>>= g) ∘ f) ≈ (>>= g) ∘ (>>= f)
    >>=-resp-≈ : ∀ {A B} {f g : ⟨ A ⟩₀ ⇒ ⟨ B ⟩} -> f ≈ g -> (>>= f) ≈ (>>= g)

  -- It could be `A' instead of ⟨ A ⟩₀.
  _<=<_ : ∀ {A B C} -> ⟨ B ⟩₀ ⇒ ⟨ C ⟩ -> ⟨ A ⟩₀ ⇒ ⟨ B ⟩ -> ⟨ A ⟩₀ ⇒ ⟨ C ⟩
  g <=< f = (>>= g) ∘ f

  _>=>_ : ∀ {A B C} -> ⟨ A ⟩₀ ⇒ ⟨ B ⟩ -> ⟨ B ⟩₀ ⇒ ⟨ C ⟩ -> ⟨ A ⟩₀ ⇒ ⟨ C ⟩
  _>=>_ = flip _<=<_
