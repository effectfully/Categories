module Categories.Functor where

open import Categories.Category

infixr 9 _∘ᶠ_

record Functor {α₁ α₂ β₁ β₂ γ₁ γ₂} (C₁ : Category α₁ β₁ γ₁) (C₂ : Category α₂ β₂ γ₂)
               : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open First C₁; open Second C₂

  field
    F· : Obj₁ -> Obj₂
    F⇒ : ∀ {A B} -> A ⇒₁ B -> F· A ⇒₂ F· B

    F-id     : ∀ {A} -> F⇒ {A} id₁ ≈₂ id₂
    F-∘      : ∀ {A B C} -> (g : B ⇒₁ C) -> (f : A ⇒₁ B) -> F⇒ (g ∘₁ f) ≈₂ F⇒ g ∘₂ F⇒ f
    F-resp-≈ : ∀ {A B} {g f : A ⇒₁ B} -> g ≈₁ f -> F⇒ g ≈₂ F⇒ f

module Heterogeneousᶠ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                      (F : Functor C₁ C₂) where
  open Functor F; open First C₁; open Second C₂

  hF-id : ∀ {A} -> F⇒ {A} id₁ ≋₂ id₂
  hF-id = hetero₂ F-id
  
  hF-∘ : ∀ {A B C} -> (g : B ⇒₁ C) -> (f : A ⇒₁ B) -> F⇒ (g ∘₁ f) ≋₂ F⇒ g ∘₂ F⇒ f
  hF-∘ g f = hetero₂ (F-∘ g f)

  F-resp-≋ : ∀ {A A' B B'} {f : A ⇒₁ B} {g : A' ⇒₁ B'} -> f ≋₁ g -> F⇒ f ≋₂ F⇒ g
  F-resp-≋ (hetero₁ f≋g) = hetero₂ (F-resp-≈ f≋g)

module _ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         (F : Functor C₁ C₂) where

  module Firstᶠ  where
    open Functor F renaming (F· to F·₁; F⇒ to F⇒₁; F-id to F-id₁; F-∘ to F-∘₁;
                             F-resp-≈ to F-resp-≈₁) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₁; hF-∘ to hF-∘₁; F-resp-≋ to F-resp-≋₁) public

  module Secondᶠ where
    open Functor F renaming (F· to F·₂; F⇒ to F⇒₂; F-id to F-id₂; F-∘ to F-∘₂;
                             F-resp-≈ to F-resp-≈₂) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₂; hF-∘ to hF-∘₂; F-resp-≋ to F-resp-≋₂) public

  module Thirdᶠ  where
    open Functor F renaming (F· to F·₃; F⇒ to F⇒₃; F-id to F-id₃; F-∘ to F-∘₃;
                             F-resp-≈ to F-resp-≈₃) public
    open Heterogeneousᶠ F renaming (hF-id to hF-id₃; hF-∘ to hF-∘₃; F-resp-≋ to F-resp-≋₃) public

Endofunctor : ∀ {α β γ} -> Category α β γ -> Set (α ⊔ β ⊔ γ)
Endofunctor C = Functor C C

_ᵒᵖᶠ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> Functor C₁ C₂ -> Functor (C₁ ᵒᵖ) (C₂ ᵒᵖ)
F ᵒᵖᶠ = record
  { F·       = F·
  ; F⇒       = F⇒
  ; F-id     = F-id
  ; F-∘      = flip F-∘
  ; F-resp-≈ = F-resp-≈
  } where open Functor F

idᶠ : ∀ {α β γ} {C : Category α β γ} -> Endofunctor C
idᶠ {C = C} = record
  { F·       = id→
  ; F⇒       = id→
  ; F-id     = irefl
  ; F-∘      = λ _ _ -> irefl
  ; F-resp-≈ = id→
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
  ; F-∘      = λ g f ->
      begin
        F⇒₂ (F⇒₁ (g ∘₁ f))         →⟨ F-resp-≈₂ (F-∘₁ g f) ⟩
        F⇒₂ (F⇒₁ g ∘₂ F⇒₁ f)       →⟨ F-∘₂ (F⇒₁ g) (F⇒₁ f) ⟩
        F⇒₂ (F⇒₁ g) ∘₃ F⇒₂ (F⇒₁ f)
      ∎
  ; F-resp-≈ = F-resp-≈₂ ∘′ F-resp-≈₁
  } where open Firstᶠ F₁; open Secondᶠ F₂
          open First C₁; open Second C₂; open Third C₃
          open IndexedEqReasoningFrom C₃

Functor-IndexedSetoid : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂}
                      -> IndexedSetoid₂ (Functor {α₁} {α₂} {β₁} {β₂} {γ₁} {γ₂}) (α₁ ⊔ β₁ ⊔ γ₂)
Functor-IndexedSetoid = record
  { _≈_                  = λ{ {C₁ , C₂} F₁ F₂ -> let open Firstᶠ F₁; open Secondᶠ F₂ in
                                 ∀ {A B} {f : A [ C₁ ]⇒ B} -> F⇒₁ f [ C₂ ]≋ F⇒₂ f
                            }
  ; isIndexedEquivalence = record
      { irefl  = λ{ {C₁ , C₂}     -> let open Heterogeneous C₂ in hrefl      }    
      ; isym   = λ{ {C₁ , C₂} p   -> let open Heterogeneous C₂ in hsym   p   }
      ; itrans = λ{ {C₁ , C₂} p q -> let open Heterogeneous C₂ in htrans p q }
      }
  }

Cat : ∀ {α β γ} -> Category (suc (α ⊔ β ⊔ γ)) (α ⊔ β ⊔ γ) (α ⊔ β ⊔ γ)
Cat {α} {β} {γ} = record
  { Obj      = Category α β γ
  ; _⇒_      = Functor
  ; setoid   = Functor-IndexedSetoid
  ; id       = idᶠ
  ; _∘_      = _∘ᶠ_
  ; idˡ      = λ {C₁ C₂}       -> let open Heterogeneous C₂ in hrefl
  ; idʳ      = λ {C₁ C₂}       -> let open Heterogeneous C₂ in hrefl
  ; assoc    = λ {C₁ C₂ C₃ C₄} -> let open Heterogeneous C₄ in hrefl
  ; ∘-resp-≈ = λ {C₁ C₂ C₃ G₁ G₂ F₁ F₂} q p {A B f} ->
      let open Functor; open Heterogeneousᶠ G₂; open MixedEqReasoningFrom C₃ in
        begin
          F⇒ G₁ (F⇒ F₁ f) →⟨ q          ⟩
          F⇒ G₂ (F⇒ F₁ f) →⟨ F-resp-≋ p ⟩
          F⇒ G₂ (F⇒ F₂ f)
        ∎
  }
