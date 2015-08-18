open import Categories.Category hiding (zero; suc)

module Categories.Object.Limit.Product {α β γ} (ℂ : Category α β γ) where

open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Cones

open import Categories.Functor.Discrete ℂ
open import Categories.Morphism         ℂ
open Category ℂ

record Product (A B : Obj) : Set (α ⊔ β ⊔ γ) where
  field
    Ob    : Obj
    π¹    : Ob ⇒ A
    π²    : Ob ⇒ B
    ⟨_,_⟩ : ∀ {C} -> C ⇒ A -> C ⇒ B -> C ⇒ Ob

    ⟨⟩-inj    : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
              -> ⟨ f₁ , g₁ ⟩ ≈ ⟨ f₂ , g₂ ⟩ -> f₁ ≈ f₂ ×ₚ g₁ ≈ g₂
    universal : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {u : C ⇒ Ob}
              -> π¹ ∘ u ≈ f -> π² ∘ u ≈ g -> ⟨ f , g ⟩ ≈ u

  η : ⟨ π¹ , π² ⟩ ≈ id
  η = universal idʳ idʳ

  ∘-η : ∀ {C} {u : C ⇒ Ob} -> ⟨ π¹ ∘ u , π² ∘ u ⟩ ≈ u
  ∘-η = universal refl refl

  π¹-⟨⟩ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π¹ ∘ ⟨ f , g ⟩ ≈ f
  π¹-⟨⟩ = proj₁ (⟨⟩-inj ∘-η)

  π²-⟨⟩ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π² ∘ ⟨ f , g ⟩ ≈ g
  π²-⟨⟩ = proj₂ (⟨⟩-inj ∘-η)
  
  ⟨⟩-∘ : ∀ {C D} {f : D ⇒ A} {g : D ⇒ B} {h : C ⇒ D} -> ⟨ f ∘ h , g ∘ h ⟩ ≈ ⟨ f , g ⟩ ∘ h
  ⟨⟩-∘ = universal (∘ˡ-resp-≈ʳ π¹-⟨⟩) (∘ˡ-resp-≈ʳ π²-⟨⟩)

  ⟨⟩-resp-≈ : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
            -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> ⟨ f₁ , g₁ ⟩ ≈ ⟨ f₂ , g₂ ⟩
  ⟨⟩-resp-≈ p q = universal (left π¹-⟨⟩ p) (left π²-⟨⟩ q)

BinaryProducts = ∀ {A B} -> Product A B

{-Limit-Product : ∀ {A B} -> Limit (Discreteᶠ (A ∷ B ∷ [])) -> Product A B
Limit-Product lim = record
  { Ob        = {!!}
  ; π¹        = {!!}
  ; π²        = {!!}
  ; _↑_       = {!!}
  ; ↑-inj     = {!!}
  ; universal = {!!}
  }
  where
    open Limit lim-}

Product-Limit : ∀ {A B} -> Product A B -> Limit (Discreteᶠ (A ∷ B ∷ []))
Product-Limit {A} {B} p = record
  { Ob        = hide record
      { η          = λ {i} -> η₀ i
      ; naturality = λ {i j p} -> naturality p
      }
  ; ↝         = λ {N i} -> ↝ N i
  ; universal = λ {N u} i -> universal₀ N u i
  } where
      open Product p

      η₀ : ∀ i -> Ob ⇒ lookup i (A ∷ B ∷ [])
      η₀  zero          = π¹
      η₀ (suc  zero)    = π²
      η₀ (suc (suc ()))

      naturality : ∀ {i j} -> (p : i ≡ j) -> η₀ j ∘ id ≈ D⇒ p ∘ η₀ i
      naturality {zero        } prefl = left idʳ idˡ
      naturality {suc  zero   } prefl = left idʳ idˡ
      naturality {suc (suc ())} prefl

      module _ (N : [ Cone Ob' _ ∣ Ob' ∈ _ ]) where
        open NaturalTransformation₁ (reveal N)

        ↝ : ∀ i -> η₁ {i} ⇒ₜ η₀ i
        ↝ i = arr , comm i where
          arr  = ⟨ η₁ {zero} , η₁ {suc zero} ⟩
          
          comm : ∀ i -> η₀ i ∘ arr ≈ η₁ {i}
          comm  zero          = π¹-⟨⟩
          comm (suc  zero)    = π²-⟨⟩
          comm (suc (suc ()))

      -- Can't unify (u {i}) with (u {zero}) and (u {suc zero}).
      -- But `i' is morally irrelevant in the first projection of (↝ N i).
      -- And we compare only first projections.
      -- But if I change the type of `u' to (∀ .{i} -> _),
      -- Agda doesn't want to reduce (η₀ zero) and thinks that it's (η₀ i),
      -- even if I make everything irrelevant.
      -- So `i' is irrelevant in a relevant context and relevant in an irrelevant context,
      -- and I have no idea how to express this in Agda.
      postulate
        universal₀ : ∀ (N : [ Cone Ob' _ ∣ Ob' ∈ _ ]) (u : ∀ {i} -> _) i -> u {i} ≈ₜ ↝ N i
     -- universal₀ N u i = sym (universal (proj₂ (u {zero})) (proj₂ (u {suc zero})))
