module Categories.Categories.Fun where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

Fun : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Category _ _ _
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

open import Categories.Category.Product

eval : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> Bifunctor (Fun C₁ C₂) C₁ C₂
eval {C₁ = C₁} {C₂ = C₂} = tag record
  { F·       = F·′
  ; F⇒       = F⇒′
  -- What happened to your pattern unification?
  ; F-id     = λ{ {F , A} -> F-id′ {F} {A} }
  ; F-∘      = λ{ {F₁ , A} {F₂ , B} {F₃ , C} {N₂ , g} {N₁ , f} ->
                     F-∘′ {F₁} {F₂} {F₃} {A} {B} {C} {g} {f} {N₂} {N₁}
                }
  ; F-resp-≈ = λ{ {F₁ , A} {F₂ , B} {N₁ , f₁} {N₂ , f₂} ->
                     F-resp-≈′ {F₁} {F₂} {A} {B} {f₁} {f₂} {N₁} {N₂}
                }
  } where
      open Category₁ C₁; open Category₂ C₂; open IEqReasoningFrom C₂; open Tools₂

      F·′ : Functor C₁ C₂ ×ₚ Obj₁ -> Obj₂
      F·′ (F , A) = F· A
        where open Functor F

      F⇒′ : ∀ {F₁ F₂ A B} -> NaturalTransformation F₁ F₂ ×ₚ A ⇒₁ B -> F·′ (F₁ , A) ⇒₂ F·′ (F₂ , B) 
      F⇒′ {F₂ = F₂} (N , f) = F⇒₂ f ∘₂ η
        where open NaturalTransformation N; open Functor₂ F₂

      F-id′ : ∀ {F A} -> F⇒′ {F₁ = F} {A = A} (idⁿ , id₁) ≈₂ id₂
      F-id′ {F} =
        begin
          F⇒ id₁ ∘₂ id₂ →⟨ idʳ₂ ⟩
          F⇒ id₁        →⟨ F-id ⟩
          id₂
        ∎
        where open Functor F

      F-∘′ : ∀ {F₁ F₂ F₃ A B C} {g : B ⇒₁ C} {f : A ⇒₁ B}
               {N₂ : NaturalTransformation F₂ F₃} {N₁ : NaturalTransformation F₁ F₂}
           -> F⇒′ (N₂ ∘ⁿ N₁ , g ∘₁ f) ≈₂ F⇒′ (N₂ , g) ∘₂ F⇒′ (N₁ , f)
      F-∘′{F₁} {F₂} {F₃} {_} {_} {_} {g} {f} {N₂} {N₁} =
        begin
          F⇒₃ (g ∘₁ f) ∘₂ η₂ ∘₂ η₁     →⟨ ∘-resp-≈ʳ F-∘₃         ⟩
          (F⇒₃ g ∘₂ F⇒₃ f) ∘₂ η₂ ∘₂ η₁ →⟨ assoc₂                 ⟩
          F⇒₃ g ∘₂ F⇒₃ f ∘₂ η₂ ∘₂ η₁   ←⟨ ∘-resp-≈ˡ assoc₂       ⟩
          F⇒₃ g ∘₂ (F⇒₃ f ∘₂ η₂) ∘₂ η₁ ←⟨ ∘-resp-≈ʳˡ naturality₂ ⟩
          F⇒₃ g ∘₂ (η₂ ∘₂ F⇒₂ f) ∘₂ η₁ →⟨ ∘-resp-≈ˡ assoc₂       ⟩
          F⇒₃ g ∘₂ η₂ ∘₂ F⇒₂ f ∘₂ η₁   ←⟨ assoc₂                 ⟩
          (F⇒₃ g ∘₂ η₂) ∘₂ F⇒₂ f ∘₂ η₁
        ∎
        where open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂
              open Functor₁ F₁; open Functor₂ F₂; open Functor₃ F₃

      open ISetoid NaturalTransformation-ISetoid renaming (_≈_ to _≈ⁿ_)

      F-resp-≈′ : ∀ {F₁ F₂ A B} {f₁ f₂ : A ⇒₁ B} {N₁ N₂ : NaturalTransformation F₁ F₂}
                -> N₁ ≈ⁿ N₂ ×ₚ f₁ ≈₁ f₂ -> F⇒′ (N₁ , f₁) ≈₂ F⇒′ (N₂ , f₂)
      F-resp-≈′ {F₂ = F₂} (r , p) = ∘-resp-≈₂ (F-resp-≈₂ p) r
        where open Functor₂ F₂
