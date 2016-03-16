open import Categories.Category
open import Categories.Functor

module Categories.Morphism.SquareOver
  {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
  {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
  (F₁ : Functor C₁ C₃) (F₂ : Functor C₂ C₃) where

open Functor₁ F₁; open Functor₂ F₂
open Category₁ C₁; open Category₂ C₂
open IEqReasoningWith C₃

infix  3 _⇒ₛ_
infixr 9 _∘ₛ_
infix  4 _≈ₛ_

_⇒ₛ_ : ∀ {A₁ A₂ B₁ B₂} -> F·₁ A₁ ⇒ F·₂ A₂ -> F·₁ B₁ ⇒ F·₂ B₂ -> Set (β₁ ⊔ β₂ ⊔ γ₃)
h₁ ⇒ₛ h₂ = ∃₂ λ f₁ f₂ -> h₂ ∘ F⇒₁ f₁ ≈ F⇒₂ f₂ ∘ h₁

idₛ : ∀ {A₁ A₂} {h : F·₁ A₁ ⇒ F·₂ A₂} -> h ⇒ₛ h
idₛ {h = h} = id₁ , id₂ , comm where
  comm = begin
           h ∘ F⇒₁ id₁ →⟨ ∘-resp-≈ˡ F-id₁ ⟩
           h ∘ id      →⟨ idʳ             ⟩
           h           ←⟨ idˡ             ⟩
           id ∘ h      ←⟨ ∘-resp-≈ʳ F-id₂ ⟩
           F⇒₂ id₂ ∘ h
         ∎

_∘ₛ_ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂} {h₁ : F·₁ A₁ ⇒ F·₂ A₂} {h₂ : F·₁ B₁ ⇒ F·₂ B₂} {h₃ : F·₁ C₁ ⇒ F·₂ C₂}
     -> h₂ ⇒ₛ h₃ -> h₁ ⇒ₛ h₂ -> h₁ ⇒ₛ h₃
_∘ₛ_ {h₁ = h₁} {h₂ = h₂} {h₃ = h₃} (g₁ , g₂ , q) (f₁ , f₂ , p) = g₁ ∘₁ f₁ , g₂ ∘₂ f₂ , comm where
  comm = begin
           h₃ ∘ F⇒₁ (g₁ ∘₁ f₁)    →⟨ ∘ʳ-resp-≈ˡ F-∘₁  ⟩ 
           (h₃ ∘ F⇒₁ g₁) ∘ F⇒₁ f₁ →⟨ ∘ʳ-resp-≈ʳ q     ⟩
           F⇒₂ g₂ ∘ h₂ ∘ F⇒₁ f₁   →⟨ ∘ʳ-resp-≈ˡ p     ⟩          
           (F⇒₂ g₂ ∘ F⇒₂ f₂) ∘ h₁ ←⟨ ∘-resp-≈ʳ  F-∘₂  ⟩
           F⇒₂ (g₂ ∘₂ f₂) ∘ h₁
         ∎

setoidₛ : ∀ {A₁ A₂ B₁ B₂} -> ISetoid₂ (_⇒ₛ_ {A₁} {A₂} {B₁} {B₂}) (γ₁ ⊔ γ₂)
setoidₛ = comapⁱˢ₁ (λ{ (f₁ , f₂ , _) -> f₁ , f₂ }) (setoid₁ ×ⁱˢ setoid₂)

_≈ₛ_ : ∀ {A₁ A₂ B₁ B₂} {h₁ : F·₁ A₁ ⇒ F·₂ A₂} {h₂ : F·₁ B₁ ⇒ F·₂ B₂}
     -> h₁ ⇒ₛ h₂ -> h₁ ⇒ₛ h₂ -> Set (γ₁ ⊔ γ₂)
_≈ₛ_ = _≈₀_
  where open ISetoid setoidₛ renaming (_≈_ to _≈₀_)
