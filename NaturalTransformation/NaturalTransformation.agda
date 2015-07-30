module Categories.NaturalTransformation.NaturalTransformation where

open import Categories.Category.Base
open import Categories.Functor.Base

infixr 9 _∘ⁿ_

record NaturalTransformation {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                             (F₁ F₂ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open Category C₂; open Functor₁ F₁; open Functor₂ F₂ 
  
  field
    η          : ∀ {O} -> F·₁ O ⇒ F·₂ O
    
    naturality : ∀ {A B} {f : A [ C₁ ]⇒ B} -> η ∘ F⇒₁ f ≈ F⇒₂ f ∘ η

module NaturalTransformation₁ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                              {Ψ Φ : Functor C₁ C₂} (N : NaturalTransformation Ψ Φ) where
  open NaturalTransformation N renaming (η to η₁; naturality to naturality₁) public

module NaturalTransformation₂ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                              {Ψ Φ : Functor C₁ C₂} (N : NaturalTransformation Ψ Φ) where
  open NaturalTransformation N renaming (η to η₂; naturality to naturality₂) public

module NaturalTransformation₃ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                              {Ψ Φ : Functor C₁ C₂} (N : NaturalTransformation Ψ Φ) where
  open NaturalTransformation N renaming (η to η₃; naturality to naturality₃) public

idⁿ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {F : Functor C₁ C₂}
    -> NaturalTransformation F F
idⁿ {C₂ = C₂} {F} = record
  { η          = id
  ; naturality = λ {A B f} ->
      begin
        id ∘ F⇒ f →⟨ idˡ ⟩
        F⇒ f      ←⟨ idʳ ⟩
        F⇒ f ∘ id
      ∎
  } where open Functor F; open IEqReasoningWith C₂

_∘ⁿ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         {Ψ : Functor C₁ C₂} {Φ : Functor C₁ C₂} {Ξ : Functor C₁ C₂}
     -> NaturalTransformation Φ Ξ -> NaturalTransformation Ψ Φ -> NaturalTransformation Ψ Ξ
_∘ⁿ_ {C₂ = C₂} {F₁} {F₂} {F₃} N₁ N₂ = record
  { η          = λ {O} -> η₁ {O} ∘ η₂ {O}
  ; naturality = λ {A B f} ->
      begin
        (η₁ ∘ η₂) ∘ F⇒₁ f →⟨ assoc                 ⟩
        η₁ ∘ (η₂ ∘ F⇒₁ f) →⟨ ∘-resp-≈ˡ naturality₂ ⟩
        η₁ ∘ (F⇒₂ f ∘ η₂) ←⟨ assoc                 ⟩
        (η₁ ∘ F⇒₂ f) ∘ η₂ →⟨ ∘-resp-≈ʳ naturality₁ ⟩
        (F⇒₃ f ∘ η₁) ∘ η₂ →⟨ assoc                 ⟩
        F⇒₃ f ∘ (η₁ ∘ η₂)
      ∎
  } where open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂
          open Functor₁ F₁; open Functor₂ F₂; open Functor₃ F₃; open IEqReasoningWith C₂

NaturalTransformation-ISetoid :
  ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
  -> ISetoid₂ (NaturalTransformation {C₁ = C₁} {C₂ = C₂}) (α₁ ⊔ γ₂)
NaturalTransformation-ISetoid {C₂ = C₂} = record
  { _≈_            = λ{ N₁ N₂ -> let open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂
                                 in ∀ {O} -> η₁ {O} ≈ η₂ {O}
                      }
  ; isIEquivalence = record
      { refl  =          refl   
      ; sym   = λ p   -> sym   p
      ; trans = λ p q -> trans p q
      }
  } where open Category C₂

Fun : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂}
    -> Category α₁ β₁ γ₁
    -> Category α₂ β₂ γ₂
    -> Category (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) (α₁ ⊔ γ₂)
Fun C₁ C₂ = record
  { Obj      = Functor C₁ C₂
  ; _⇒_      = NaturalTransformation
  ; setoid   = NaturalTransformation-ISetoid
  ; id       = idⁿ
  ; _∘_      = _∘ⁿ_
  ; idˡ      = idˡ
  ; idʳ      = idʳ
  ; assoc    = assoc
  ; ∘-resp-≈ = λ q p -> ∘-resp-≈ q p
  } where open NaturalTransformation; open Category C₂
