open import Categories.Category hiding (zero; suc)

module Categories.Object.Limit.Properties.Product {α β γ} (ℂ : Category α β γ) where

open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Categories.Comma
open import Categories.Object.Zoo

open import Categories.Object.Limit.Product ℂ
open import Categories.Functor.Discrete     ℂ

open IEqReasoningWith ℂ

module _ {A B} where
  2ᶠ = discreteᶠ (A ∷ B ∷ [])

  Product-Limit : Product A B -> Limit 2ᶠ
  Product-Limit p = record
    { Ob     = , , record
        { η          = λ {i} -> η₀ i
        ; naturality = λ {i j i≡j} -> naturality i≡j
        }
    ; ↝      = λ {C} -> ↝ C , prefl , left (comm C) idˡ
    ; ↝-univ = λ {C u} -> ↝-univ₀ C u , _
    } where
        open Product p

        η₀ : ∀ i -> Ob ⇒ lookup i (A ∷ B ∷ [])
        η₀  zero          = π¹
        η₀ (suc  zero)    = π²
        η₀ (suc (suc ()))

        naturality : ∀ {i j} -> (i≡j : i ≡ j) -> η₀ j ∘ id ≈ D⇒ i≡j ∘ η₀ i
        naturality prefl = left idʳ idˡ

        module _ (C : ∃₂ λ Ob' _ -> Cone Ob' 2ᶠ) where
          open NaturalTransformation₁ (proj₂ (proj₂ C))

          ↝ = ⟨ η₁ {zero} , η₁ {suc zero} ⟩

          comm : ∀ {i} -> η₀ i ∘ ↝ ≈ η₁ {i}
          comm {zero        } = π¹-⟨⟩
          comm {suc  zero   } = π²-⟨⟩
          comm {suc (suc ())}

          ↝-univ₀ : ∀ u -> proj₁ u ≈ ↝
          ↝-univ₀ u = sym (⟨⟩-univ (proj₂ (proj₂ u) {zero    } ⋯ idˡ)
                                   (proj₂ (proj₂ u) {suc zero} ⋯ idˡ))

  Limit-Product : Limit 2ᶠ -> Product A B
  Limit-Product lim = record
    { Ob      = Ob₂
    ; π¹      = η₁ {zero}
    ; π²      = η₁ {suc zero}
    ; ⟨_,_⟩   = λ f g -> proj₁ ⟨ f ⇣ g ⟩
    ; ⟨⟩-inj  = ⟨⟩-inj
    ; ⟨⟩-univ = ⟨⟩-univ₂
    } where
        open Limit lim
        open NaturalTransformation₁ (proj₂ (proj₂ Ob))

        Ob₂ = proj₁ Ob

        η₂ : ∀ {C} i -> C ⇒ A -> C ⇒ B -> C ⇒ lookup i (A ∷ B ∷ [])
        η₂  zero          f g = f
        η₂ (suc zero)     f g = g
        η₂ (suc (suc ())) f g

        naturality₂ : ∀ {C i j} {f : C ⇒ A} {g : C ⇒ B}
                    -> (i≡j : i ≡ j) -> η₂ j f g ∘ id ≈ D⇒ i≡j ∘ η₂ i f g
        naturality₂ prefl = left idʳ idˡ

        ⟨_⇣_⟩ : ∀ {C} -> (f : C ⇒ A) -> (g : C ⇒ B) -> _
        ⟨ f ⇣ g ⟩ = ↝ {_ , _ , record
            { η          = λ {i} -> η₂ i f g
            ; naturality = λ {i j i≡j} -> naturality₂ i≡j
            }
          }

        ⟨⟩-inj : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
               -> proj₁ ⟨ f₁ ⇣ g₁ ⟩ ≈ proj₁ ⟨ f₂ ⇣ g₂ ⟩ -> f₁ ≈ f₂ ×ₚ g₁ ≈ g₂
        ⟨⟩-inj {C} {f₁} {f₂} {g₁} {g₂} p = (
            begin
              f₁           ←⟨ idˡ                                  ⟩
              id ∘ f₁      ←⟨ proj₂ (proj₂ ⟨ f₁ ⇣ g₁ ⟩) {zero}     ⟩
              η₁ ∘ proj₁ ↝ →⟨ ∘-resp-≈ˡ p                          ⟩
              η₁ ∘ proj₁ ↝ →⟨ proj₂ (proj₂ ⟨ f₂ ⇣ g₂ ⟩) {zero}     ⟩
              id ∘ f₂      →⟨ idˡ                                  ⟩
              f₂
            ∎
          ) , (
            begin
              g₁           ←⟨ idˡ                                  ⟩
              id ∘ g₁      ←⟨ proj₂ (proj₂ ⟨ f₁ ⇣ g₁ ⟩) {suc zero} ⟩
              η₁ ∘ proj₁ ↝ →⟨ ∘-resp-≈ˡ p                          ⟩
              η₁ ∘ proj₁ ↝ →⟨ proj₂ (proj₂ ⟨ f₂ ⇣ g₂ ⟩) {suc zero} ⟩
              id ∘ g₂      →⟨ idˡ                                  ⟩
              g₂
            ∎
          )

        ⟨⟩-univ₂ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {u : C ⇒ Ob₂}
                   -> η₁ ∘ u ≈ f -> η₁ ∘ u ≈ g -> proj₁ ⟨ f ⇣ g ⟩ ≈ u
        ⟨⟩-univ₂ {C} {f} {g} {u} p q = sym (proj₁ (↝-univ {_} {u , prefl , ⟨⟩-univ})) where
          ⟨⟩-univ : ∀ {i} -> η₁ {i} ∘ u ≈ id ∘ η₂ i f g
          ⟨⟩-univ {zero        } = left p idˡ
          ⟨⟩-univ {suc  zero   } = left q idˡ
          ⟨⟩-univ {suc (suc ())}
