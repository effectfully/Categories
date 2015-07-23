open import Categories.Category

module Categories.Universal.Limit.Pullback {α β γ} (C : Category α β γ) where

open import Data.Product

open Category C

record Pullback {A B C : Obj} (f : A ⇒ C) (g : B ⇒ C) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↘_

  field
    A×B : Obj
    π₁  : A×B ⇒ A
    π₂  : A×B ⇒ B   
    _↘_ : ∀ {D} -> D ⇒ A -> D ⇒ B -> D ⇒ A×B

    comm     : f ∘ π₁ ≈ g ∘ π₂
    ↘-inj    : ∀ {D} {p₁ p₂ : D ⇒ A} {q₁ q₂ : D ⇒ B}
             -> p₁ ↘ q₁ ≈ p₂ ↘ q₂ -> p₁ ≈ p₂ × q₁ ≈ q₂
    universal : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} {u : D ⇒ A×B}
              -> π₁ ∘ u ≈ p -> π₂ ∘ u ≈ q -> p ↘ q ≈ u

  η : π₁ ↘ π₂ ≈ id
  η = universal idʳ idʳ

  ∘-η : ∀ {D} {u : D ⇒ A×B} -> π₁ ∘ u ↘ π₂ ∘ u ≈ u
  ∘-η = universal irefl irefl

  π₁-↘ : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} -> π₁ ∘ (p ↘ q) ≈ p
  π₁-↘ = proj₁ (↘-inj ∘-η)

  π₂-↘ : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} -> π₂ ∘ (p ↘ q) ≈ q
  π₂-↘ = proj₂ (↘-inj ∘-η)

  ↑-resp-≈ : ∀ {D} {p₁ p₂ : D ⇒ A} {q₁ q₂ : D ⇒ B}
           -> p₁ ≈ p₂ -> q₁ ≈ q₂ -> p₁ ↘ q₁ ≈ p₂ ↘ q₂
  ↑-resp-≈ r s = universal (itrans π₁-↘ (isym r)) (itrans π₂-↘ (isym s))
