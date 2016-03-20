module Categories.Functor.Zoo where

open import Categories.Category
open import Categories.Functor.Core
open import Categories.Categories.Discrete

Endofunctor : ∀ {α β γ} -> Category α β γ -> Set _
Endofunctor C = Functor C C

Contravariant : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Set _
Contravariant C D = Functor (C ᵒᵖ) D

Faithful : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
         -> (F : Functor C₁ C₂) -> Set _
Faithful {C₁ = C₁} {C₂ = C₂} F = ∀ {A B} {f g : A ⇒₁ B} -> F⇒ f ≈₂ F⇒ g -> f ≈₁ g
  where open Functor F; open Category₁ C₁; open Category₂ C₂

Full : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
     -> (F : Functor C₁ C₂) -> Set _
Full {C₂ = C₂} F = ∀ {A B} -> (g : F· A ⇒ F· B) -> ∃ λ f -> F⇒ f ≈ g
  where open Functor F; open Category C₂

Bifunctor : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
          -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Category α₃ β₃ γ₃ -> Set _
Bifunctor = Tag₃ λ C₁ C₂ C₃ -> Functor (C₁ ×ᶜ C₂) C₃

pointᶠ : ∀ {α β γ} {C : Category α β γ} -> _ -> Functor One C
pointᶠ = constᶠ
 
reduceᶠ : ∀ {α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ γ₁ γ₂ γ₃ γ₄}
            {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
            {C₃ : Category α₃ β₃ γ₃} {C₄ : Category α₄ β₄ γ₄}
        -> Bifunctor C₁ C₂ C₃ -> Functor C₄ C₁ -> Functor C₄ C₂ -> Functor C₄ C₃
reduceᶠ F₁ F₂ F₃ = detag F₁ ∘ᶠ (F₂ ※ F₃)

reduceᶠˡ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
             {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
         -> Bifunctor C₁ C₂ C₃ -> Functor C₂ C₁ -> Functor C₂ C₃
reduceᶠˡ F₁ F₂ = reduceᶠ F₁ F₂ idᶠ

reduceᶠʳ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
             {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
         -> Bifunctor C₁ C₂ C₃ -> Functor C₁ C₂ -> Functor C₁ C₃
reduceᶠʳ F₁ F₂ = reduceᶠ F₁ idᶠ F₂

applyᶠˡ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
            {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
        -> Bifunctor C₁ C₂ C₃ -> _ -> Functor C₂ C₃
applyᶠˡ F A₁ = reduceᶠˡ F (constᶠ A₁)

applyᶠʳ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃ γ₁ γ₂ γ₃}
            {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
        -> Bifunctor C₁ C₂ C₃ -> _ -> Functor C₁ C₃
applyᶠʳ F A₂ = reduceᶠʳ F (constᶠ A₂)

composeᶠ : ∀ {α₁ α₂ α₃ α₄ α₅ β₁ β₂ β₃ β₄ β₅ γ₁ γ₂ γ₃ γ₄ γ₅}
             {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂} {C₃ : Category α₃ β₃ γ₃}
             {C₄ : Category α₄ β₄ γ₄} {C₅ : Category α₅ β₅ γ₅}
         -> Bifunctor C₁ C₂ C₃ -> Functor C₄ C₁ -> Functor C₅ C₂ -> Bifunctor C₄ C₅ C₃
composeᶠ F₁ F₂ F₃ = tag (detag F₁ ∘ᶠ (F₂ ⁂ F₃))

