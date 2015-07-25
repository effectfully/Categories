open import Categories.Category

module Categories.Universal.Colimit.Pushout {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open Category ℂ

record Pushout {A B C : Obj} (f : C ⇒ A) (g : C ⇒ B) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↖_

  field
    Ob  : Obj
    ι₁  : A ⇒ Ob
    ι₂  : B ⇒ Ob
    _↖_ : ∀ {D} -> A ⇒ D -> B ⇒ D -> Ob ⇒ D

    comm      : ι₁ ∘ f ≈ ι₂ ∘ g
    ↖-inj     : ∀ {D} {p₁ p₂ : A ⇒ D} {q₁ q₂ : B ⇒ D}
              -> p₁ ↖ q₁ ≈ p₂ ↖ q₂ -> p₁ ≈ p₂ × q₁ ≈ q₂
    universal : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {u : Ob ⇒ D}
              -> u ∘ ι₁ ≈ p -> u ∘ ι₂ ≈ q -> p ↖ q ≈ u

  η : ι₁ ↖ ι₂ ≈ id
  η = universal idˡ idˡ

  ∘-η : ∀ {D} {u : Ob ⇒ D} -> u ∘ ι₁ ↖ u ∘ ι₂ ≈ u
  ∘-η = universal refl refl

  ↖-ι₁ : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} -> (p ↖ q) ∘ ι₁ ≈ p
  ↖-ι₁ = proj₁ (↖-inj ∘-η)

  ↖-ι₂ : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} -> (p ↖ q) ∘ ι₂ ≈ q
  ↖-ι₂ = proj₂ (↖-inj ∘-η)

  ↖-∘ : ∀ {D E} {p : A ⇒ D} {q : B ⇒ D} {r : D ⇒ E} -> (r ∘ p) ↖ (r ∘ q) ≈ r ∘ (p ↖ q)
  ↖-∘ = universal (∘ˡ-resp-≈ˡ ↖-ι₁) (∘ˡ-resp-≈ˡ ↖-ι₂)

  ↖-resp-≈ : ∀ {D} {p₁ p₂ : A ⇒ D} {q₁ q₂ : B ⇒ D}
           -> p₁ ≈ p₂ -> q₁ ≈ q₂ -> p₁ ↖ q₁ ≈ p₂ ↖ q₂
  ↖-resp-≈ p q = universal (left ↖-ι₁ p) (left ↖-ι₂ q)