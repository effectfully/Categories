module Categories.Functor.Functor where

open import Categories.Category
open import Categories.Category.Product

infixr 9 _∘ᶠ_
infixr 6 _⁂_ _※_

record Functor {α₁ α₂ β₁ β₂ γ₁ γ₂} (C₁ : Category α₁ β₁ γ₁) (C₂ : Category α₂ β₂ γ₂)
               : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open Category₁ C₁; open Category₂ C₂

  field
    F· : Obj₁ -> Obj₂
    F⇒ : ∀ {A B} -> A ⇒₁ B -> F· A ⇒₂ F· B

    F-id     : ∀ {A} -> F⇒ {A} id₁ ≈₂ id₂
    F-∘      : ∀ {A B C} {g : B ⇒₁ C} {f : A ⇒₁ B} -> F⇒ (g ∘₁ f) ≈₂ F⇒ g ∘₂ F⇒ f
    F-resp-≈ : ∀ {A B} {g f : A ⇒₁ B} -> g ≈₁ f -> F⇒ g ≈₂ F⇒ f

module Heterogeneousᶠ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                      (F : Functor C₁ C₂) where
  open Functor F; open Category₁ C₁; open Category₂ C₂

  hF-id : ∀ {A} -> F⇒ {A} id₁ ≋₂ id₂
  hF-id = hetero₂ F-id
  
  hF-∘ : ∀ {A B C} -> (g : B ⇒₁ C) -> (f : A ⇒₁ B) -> F⇒ (g ∘₁ f) ≋₂ F⇒ g ∘₂ F⇒ f
  hF-∘ g f = hetero₂ F-∘

  F-resp-≋ : ∀ {A A' B B'} {f : A ⇒₁ B} {g : A' ⇒₁ B'} -> f ≋₁ g -> F⇒ f ≋₂ F⇒ g
  F-resp-≋ (hetero₁ f≋g) = hetero₂ (F-resp-≈ f≋g)

module _ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         (F : Functor C₁ C₂) where
  module Functor₁ where
    open Functor F renaming (F· to F·₁; F⇒ to F⇒₁; F-id to F-id₁; F-∘ to F-∘₁;
                             F-resp-≈ to F-resp-≈₁) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₁; hF-∘ to hF-∘₁; F-resp-≋ to F-resp-≋₁) public

  module Functor₂ where
    open Functor F renaming (F· to F·₂; F⇒ to F⇒₂; F-id to F-id₂; F-∘ to F-∘₂;
                             F-resp-≈ to F-resp-≈₂) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₂; hF-∘ to hF-∘₂; F-resp-≋ to F-resp-≋₂) public

  module Functor₃ where
    open Functor F renaming (F· to F·₃; F⇒ to F⇒₃; F-id to F-id₃; F-∘ to F-∘₃;
                             F-resp-≈ to F-resp-≈₃) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₃; hF-∘ to hF-∘₃; F-resp-≋ to F-resp-≋₃) public

  module Functor₄ where
    open Functor F renaming (F· to F·₄; F⇒ to F⇒₄; F-id to F-id₄; F-∘ to F-∘₄;
                             F-resp-≈ to F-resp-≈₄) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₄; hF-∘ to hF-∘₄; F-resp-≋ to F-resp-≋₄) public

_ᶠᵒᵖ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> Functor C₁ C₂ -> Functor (C₁ ᵒᵖ) (C₂ ᵒᵖ)
F ᶠᵒᵖ = record
  { F·       = F·
  ; F⇒       = F⇒
  ; F-id     = F-id
  ; F-∘      = F-∘
  ; F-resp-≈ = F-resp-≈
  } where open Functor F

idᶠ : ∀ {α β γ} {C : Category α β γ} -> Functor C C
idᶠ {C = C} = record
  { F·       = id′
  ; F⇒       = id′
  ; F-id     = refl
  ; F-∘      = refl
  ; F-resp-≈ = id′
  } where open Category C

_∘ᶠ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
         {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
     -> Functor C₂ C₃ -> Functor C₁ C₂ -> Functor C₁ C₃
_∘ᶠ_ {C₁ = C₁} {C₂ = C₂} {C₃ = C₃} F₂ F₁ = record
  { F·       = F·₂ ∘′ F·₁
  ; F⇒       = F⇒₂ ∘′ F⇒₁
  ; F-id     =
      begin
        F⇒₂ (F⇒₁ id₁) →⟨ F-resp-≈₂ F-id₁ ⟩
        F⇒₂  id₂      →⟨ F-id₂           ⟩
        id₃
      ∎
  ; F-∘      = λ {_ _ _ g f} ->
      begin
        F⇒₂ (F⇒₁ (g ∘₁ f))         →⟨ F-resp-≈₂ F-∘₁ ⟩
        F⇒₂ (F⇒₁ g ∘₂ F⇒₁ f)       →⟨ F-∘₂           ⟩
        F⇒₂ (F⇒₁ g) ∘₃ F⇒₂ (F⇒₁ f)
      ∎
  ; F-resp-≈ = F-resp-≈₂ ∘′ F-resp-≈₁
  } where open Functor₁ F₁; open Functor₂ F₂
          open Category₁ C₁; open Category₂ C₂; open Category₃ C₃; open IEqReasoningFrom C₃

constᶠ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
       -> _ -> Functor C₁ C₂
constᶠ {C₂ = C₂} A₂ = record
  { F·       = const A₂
  ; F⇒       = const id
  ; F-id     = refl
  ; F-∘      = sym idʳ
  ; F-resp-≈ = λ _ -> refl
  } where open Category C₂

_※_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
        {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
    -> Functor C₁ C₂ -> Functor C₁ C₃ -> Functor C₁ (C₂ × C₃)
F₁ ※ F₂ = record
  { F·       = < F·₁ , F·₂ >
  ; F⇒       = < F⇒₁ , F⇒₂ >
  ; F-id     = F-id₁ , F-id₂
  ; F-∘      = F-∘₁ , F-∘₂
  ; F-resp-≈ = < F-resp-≈₁ , F-resp-≈₂ >
  } where open Functor₁ F₁; open Functor₂ F₂

_⁂_ : ∀ {α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ γ₁ γ₂ γ₃ γ₄}
        {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
        {C₃ : Category α₃ β₃ γ₃} {C₄ : Category α₄ β₄ γ₄}
    -> Functor C₁ C₂ -> Functor C₃ C₄ -> Functor (C₁ × C₃) (C₂ × C₄)
F₁ ⁂ F₂ = record
  { F·       = map F·₁ F·₂
  ; F⇒       = map F⇒₁ F⇒₂
  ; F-id     = F-id₁ , F-id₂
  ; F-∘      = F-∘₁  , F-∘₂
  ; F-resp-≈ = map F-resp-≈₁ F-resp-≈₂
  } where open Functor₁ F₁; open Functor₂ F₂

setoidᶠ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} -> ISetoid₂ (Functor {α₁} {α₂} {β₁} {β₂} {γ₁} {γ₂}) (α₁ ⊔ β₁ ⊔ γ₂)
setoidᶠ = record
  { _≈_            = λ{ {C₁ , C₂} F₁ F₂ -> let open Functor₁ F₁; open Functor₂ F₂ in
                                 ∀ {A B} {f : A [ C₁ ]⇒ B} -> F⇒₁ f [ C₂ ]≋ F⇒₂ f
                      }
  ; isIEquivalence = record
      { refl  = λ{ {C₁ , C₂}     -> Heterogeneous.hrefl  C₂     }    
      ; sym   = λ{ {C₁ , C₂} p   -> Heterogeneous.hsym   C₂ p   }
      ; trans = λ{ {C₁ , C₂} p q -> Heterogeneous.htrans C₂ p q }
      }
  }
