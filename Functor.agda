module Categories.Functor where

import Function as F

open import Categories.Category

infixr 9 _∘ᶠ_

record Functor {α₁ α₂ β₁ β₂ γ₁ γ₂} (C₁ : Category α₁ β₁ γ₁) (C₂ : Category α₂ β₂ γ₂)
               : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  open First C₁; open Second C₂

  field
    F₀ : Obj₁ -> Obj₂
    F₁ : ∀ {A B} -> A ⇒₁ B -> F₀ A ⇒₂ F₀ B

    F-id     : ∀ {A} -> F₁ {A} id₁ ≈₂ id₂
    F-∘      : ∀ {A B C} -> (g : B ⇒₁ C) -> (f : A ⇒₁ B) -> F₁ (g ∘₁ f) ≈₂ F₁ g ∘₂ F₁ f
    F-resp-≈ : ∀ {A B} {g f : A ⇒₁ B} -> g ≈₁ f -> F₁ g ≈₂ F₁ f

module Phi {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
           (F : Functor C₁ C₂) where
  open Functor F renaming (F₀ to Φ₀; F₁ to Φ₁; F-id to Φ-id; F-∘ to Φ-∘; F-resp-≈ to Φ-resp-≈) public

module Psi {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
           (F : Functor C₁ C₂) where
  open Functor F renaming (F₀ to Ψ₀; F₁ to Ψ₁; F-id to Ψ-id; F-∘ to Ψ-∘; F-resp-≈ to Ψ-resp-≈) public

module Heterogeneousᶠ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                      (F : Functor C₁ C₂) where
  open Functor F; open First C₁; open Second C₂

  hF-id : ∀ {A} -> F₁ {A} id₁ ≋₂ id₂
  hF-id = hetero₂ F-id
  
  hF-∘ : ∀ {A B C} -> (g : B ⇒₁ C) -> (f : A ⇒₁ B) -> F₁ (g ∘₁ f) ≋₂ F₁ g ∘₂ F₁ f
  hF-∘ g f = hetero₂ (F-∘ g f)

  F-resp-≋ : ∀ {A A' B B'} {f : A ⇒₁ B} {g : A' ⇒₁ B'} -> f ≋₁ g -> F₁ f ≋₂ F₁ g
  F-resp-≋ (hetero₁ f≋g) = hetero₂ (F-resp-≈ f≋g)

Endofunctor : ∀ {α β γ} -> Category α β γ -> Set (α ⊔ β ⊔ γ)
Endofunctor C = Functor C C

_ᵒᵖᶠ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> Functor C₁ C₂ -> Functor (C₁ ᵒᵖ) (C₂ ᵒᵖ)
F ᵒᵖᶠ = record
  { F₀       = F₀
  ; F₁       = F₁
  ; F-id     = F-id
  ; F-∘      = flip F-∘
  ; F-resp-≈ = F-resp-≈
  } where open Functor F

idᶠ : ∀ {α β γ} {C : Category α β γ} -> Endofunctor C
idᶠ {C = C} = record
  { F₀       = F.id
  ; F₁       = F.id
  ; F-id     = irefl
  ; F-∘      = λ _ _ -> irefl
  ; F-resp-≈ = F.id
  } where open IndexedSetoidFrom C

_∘ᶠ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
         {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
     -> Functor C₂ C₃ -> Functor C₁ C₂ -> Functor C₁ C₃
_∘ᶠ_ {C₁ = C₁} {C₂ = C₂} {C₃ = C₃} Φ Ψ = record
  { F₀       = Φ₀ F.∘ Ψ₀
  ; F₁       = Φ₁ F.∘ Ψ₁
  ; F-id     =
      begin
        Φ₁ (Ψ₁ id₁) →⟨ Φ-resp-≈ Ψ-id ⟩
        Φ₁  id₂     →⟨ Φ-id          ⟩
        id₃
      ∎
  ; F-∘      = λ g f ->
      begin
        Φ₁ (Ψ₁ (g ∘₁ f))       →⟨ Φ-resp-≈ (Ψ-∘ g f) ⟩
        Φ₁ (Ψ₁ g ∘₂ Ψ₁ f)      →⟨ Φ-∘ (Ψ₁ g) (Ψ₁ f)  ⟩
        Φ₁ (Ψ₁ g) ∘₃ Φ₁ (Ψ₁ f)
      ∎
  ; F-resp-≈ = Φ-resp-≈ F.∘ Ψ-resp-≈
  } where open Phi Φ; open Psi Ψ
          open First C₁; open Second C₂; open Third C₃
          open IndexedEqReasoningFrom C₃

Functor-IndexedSetoid : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂}
                      -> IndexedSetoid (uncurry (Functor {α₁} {α₂} {β₁} {β₂} {γ₁} {γ₂}))
                                       (α₁ ⊔ β₁ ⊔ γ₂)
Functor-IndexedSetoid = record
  { _≈_                  = λ{ {C₁ , C₂} Φ Ψ ->
                                 let open Phi Φ; open Psi Ψ; open First C₁; open Second C₂
                                 in ∀ {A B} {f : A ⇒₁ B} -> Φ₁ f ≋₂ Ψ₁ f
                            }
  ; isIndexedEquivalence = record
      { irefl  = λ{ {C₁ , C₂}     -> let open Heterogeneous C₂ in hrefl      }    
      ; isym   = λ{ {C₁ , C₂} p   -> let open Heterogeneous C₂ in hsym p     }
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
  ; idˡ      = λ {C₁ C₂}         -> let open Heterogeneous C₂ in hrefl
  ; idʳ      = λ {C₁ C₂}         -> let open Heterogeneous C₂ in hrefl
  ; assoc    = λ {C₁ C₂ C₃ C₄} _ -> let open Heterogeneous C₄ in hrefl
  ; ∘-resp-≈ = λ {C₁ C₂ C₃ Φ₁ Φ₂ Ψ₁ Ψ₂} q p {A B f} ->
      let open Functor; open Heterogeneousᶠ Φ₂; open MixedEqReasoningFrom C₃ in
        begin
          F₁ Φ₁ (F₁ Ψ₁ f) →⟨ q ⟩
          F₁ Φ₂ (F₁ Ψ₁ f) →⟨ F-resp-≋ p ⟩
          F₁ Φ₂ (F₁ Ψ₂ f)
        ∎
  }
