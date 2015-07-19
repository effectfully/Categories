module Categories.NaturalTransformation where

open import Categories.Category
open import Categories.Functor

infixr 9 _∘ⁿ_

record NaturalTransformation {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                             (F₁ F₂ : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open Category C₂; open Firstᶠ F₁; open Secondᶠ F₂ 
  
  field
    η          : ∀ {O} -> F·₁ O ⇒ F·₂ O
    naturality : ∀ {A B} {f : A [ C₁ ]⇒ B} -> η ∘ F⇒₁ f ≈ F⇒₂ f ∘ η

module Firstⁿ  {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
               {Ψ Φ : Functor C₁ C₂} (N : NaturalTransformation Ψ Φ) where
  open NaturalTransformation N renaming (η to η₁; naturality to naturality₁) public

module Secondⁿ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
               {Ψ Φ : Functor C₁ C₂} (N : NaturalTransformation Ψ Φ) where
  open NaturalTransformation N renaming (η to η₂; naturality to naturality₂) public

module Thirdⁿ  {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
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
  } where open Functor F; open Category C₂; open IndexedEqReasoningFrom C₂

-- Vertical.
_∘ⁿ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         {Ψ : Functor C₁ C₂} {Φ : Functor C₁ C₂} {Ξ : Functor C₁ C₂}
  -> NaturalTransformation Φ Ξ -> NaturalTransformation Ψ Φ -> NaturalTransformation Ψ Ξ
_∘ⁿ_ {C₂ = C₂} {F₁} {F₂} {F₃} N₁ N₂ = record
  { η          = λ {O} -> η₁ {O} ∘ η₂ {O}
  ; naturality = λ {A B f} ->
      begin
        (η₁ ∘ η₂) ∘ F⇒₁ f →⟨ assoc η₁                   ⟩
        η₁ ∘ (η₂ ∘ F⇒₁ f) →⟨ ∘-resp-≈ irefl naturality₂ ⟩
        η₁ ∘ (F⇒₂ f ∘ η₂) ←⟨ assoc η₁                   ⟩
        (η₁ ∘ F⇒₂ f) ∘ η₂ →⟨ ∘-resp-≈ naturality₁ irefl ⟩
        (F⇒₃ f ∘ η₁) ∘ η₂ →⟨ assoc (F⇒₃ f)              ⟩
        F⇒₃ f ∘ (η₁ ∘ η₂)
      ∎
  } where open Firstⁿ N₁; open Secondⁿ N₂
          open Firstᶠ F₁; open Secondᶠ F₂; open Thirdᶠ F₃
          open Category C₂; open IndexedSetoid setoid; open IndexedEqReasoningFrom C₂

NaturalTransformation-IndexedSetoid :
  ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
  -> IndexedSetoid (uncurry (NaturalTransformation {C₁ = C₁} {C₂ = C₂})) (α₁ ⊔ γ₂)
NaturalTransformation-IndexedSetoid {C₂ = C₂} = record
  { _≈_                  = λ{ N₁ N₂ -> let open Firstⁿ N₁; open Secondⁿ N₂ in
                                 ∀ {O} -> η₁ {O} ≈ η₂ {O}
                            }
  ; isIndexedEquivalence = record
      { irefl  =          irefl   
      ; isym   = λ p   -> isym p
      ; itrans = λ p q -> itrans p q
      }
  } where open IndexedSetoidFrom C₂

Fun : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
        -> Category (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) (α₁ ⊔ γ₂)
Fun {C₁ = C₁} {C₂ = C₂} = record
  { Obj      = Functor C₁ C₂
  ; _⇒_      = NaturalTransformation
  ; setoid   = NaturalTransformation-IndexedSetoid
  ; id       = idⁿ
  ; _∘_      = _∘ⁿ_
  ; idˡ      = idˡ
  ; idʳ      = idʳ
  ; assoc    = λ _ -> assoc _
  ; ∘-resp-≈ = λ q p -> ∘-resp-≈ q p
  } where open NaturalTransformation; open Category C₂
