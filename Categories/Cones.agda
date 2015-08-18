module Categories.Categories.Cones where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Object.Zoo using (Cone) public
open import Categories.Object.Limit.Terminal

Cones : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
      -> Functor C₁ C₂ -> Category _ _ _
Cones {C₂ = C₂} F = record
  { Obj      = [ Cone A₂ F ∣ A₂ ∈ Obj ]
  ; _⇒_      = λ{ (hide N₁) (hide N₂) ->
                   let open NaturalTransformation₁ N₁; open NaturalTransformation₂ N₂ in
                        ∀ {A₁} -> η₁ {A₁} ⇒ₜ η₂ {A₁}
                }
  ; setoid   = comap∀ⁱˢₑ (λ A₁ p -> proj₁ (p {A₁})) setoid
  ; id       = idₜ
  ; _∘_      = λ q p -> q ∘ₜ p
  ; idˡ      = λ _ -> idˡ
  ; idʳ      = λ _ -> idʳ
  ; assoc    = λ _ -> assoc
  ; ∘-resp-≈ = λ q p A -> ∘-resp-≈ (q A) (p A)
  } where open import Categories.Morphism C₂
          open Category C₂

Limit : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
      -> (F : Functor C₁ C₂) -> Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂)
Limit F = Terminal (Cones F)

module Limit {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
             {F : Functor C₁ C₂} = Terminal (Cones F)
