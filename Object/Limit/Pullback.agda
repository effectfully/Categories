open import Categories.Category

module Categories.Object.Limit.Pullback {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism ℂ

open Category ℂ

record Pullback {A B C : Obj} (f : A ⇒ C) (g : B ⇒ C) : Set (α ⊔ β ⊔ γ) where
  field
    Ob       : Obj
    π¹       : Ob ⇒ A
    π²       : Ob ⇒ B   
    ⟨_,_⟩∣_∣ : ∀ {D} -> (p : D ⇒ A) -> (q : D ⇒ B) -> .(f ∘ p ≈ g ∘ q) -> D ⇒ Ob

    .comm      : f ∘ π¹ ≈ g ∘ π²
    .⟨⟩-inj    : ∀ {D} {p₁ p₂ : D ⇒ A} {q₁ q₂ : D ⇒ B} {r : f ∘ p₁ ≈ g ∘ q₁} {s : f ∘ p₂ ≈ g ∘ q₂}
               -> ⟨ p₁ , q₁ ⟩∣ r ∣ ≈ ⟨ p₂ , q₂ ⟩∣ s ∣ -> p₁ ≈ p₂ ×ₚ q₁ ≈ q₂
    .universal : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} {u : D ⇒ Ob}
               -> (r : π¹ ∘ u ≈ p) -> (s : π² ∘ u ≈ q) -> ⟨ p , q ⟩∣ r ⌈ ∘²-resp-≈ʳ comm ⌉ʳ s ∣ ≈ u

  .η : ⟨ π¹ , π² ⟩∣ _ ∣ ≈ id
  η = universal idʳ idʳ

  .∘-η : ∀ {D} {u : D ⇒ Ob} -> ⟨ π¹ ∘ u , π² ∘ u ⟩∣ _ ∣ ≈ u
  ∘-η = universal refl refl

  .π-inj : ∀ {D} {p : D ⇒ Ob} {q : D ⇒ Ob}
         -> π¹ ∘ p ≈ π¹ ∘ q -> π² ∘ p ≈ π² ∘ q -> p ≈ q
  π-inj r s = right (universal r s) ∘-η

  .π¹-⟨⟩ : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} {r : f ∘ p ≈ g ∘ q} -> π¹ ∘ ⟨ p , q ⟩∣ r ∣ ≈ p
  π¹-⟨⟩ = proj₁ (⟨⟩-inj ∘-η)

  .π²-⟨⟩ : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} {r : f ∘ p ≈ g ∘ q} -> π² ∘ ⟨ p , q ⟩∣ r ∣ ≈ q
  π²-⟨⟩ = proj₂ (⟨⟩-inj ∘-η)

  .⟨⟩-∘ : ∀ {D E} {r : D ⇒ E} {p : E ⇒ A} {q : E ⇒ B} {s : f ∘ p ≈ g ∘ q}
        -> ⟨ p ∘ r , q ∘ r ⟩∣ _ ∣ ≈ ⟨ p , q ⟩∣ s ∣ ∘ r 
  ⟨⟩-∘ = universal (∘ˡ-resp-≈ʳ π¹-⟨⟩) (∘ˡ-resp-≈ʳ π²-⟨⟩)

  .⟨⟩-resp-≈ : ∀ {D} {p₁ p₂ : D ⇒ A} {q₁ q₂ : D ⇒ B} {r : f ∘ p₁ ≈ g ∘ q₁}
             -> (s : p₁ ≈ p₂) -> (t : q₁ ≈ q₂) -> ⟨ p₁ , q₁ ⟩∣ r ∣ ≈ ⟨ p₂ , q₂ ⟩∣ s ⌈ r ⌉ʳ t ∣
  ⟨⟩-resp-≈ r s = universal (left π¹-⟨⟩ r) (left π²-⟨⟩ s)

  .π¹-Mono : Mono g -> Mono π¹
  π¹-Mono mono = λ r -> π-inj r (mono (comm ²⌈ ∘-resp-≈ˡ r ⌉ˡ comm))

-- There is a proper name, but I forgot it.
flip-Pullback : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} -> Pullback f g -> Pullback g f
flip-Pullback p = record
  { Ob        = Ob
  ; π¹        = π²
  ; π²        = π¹
  ; ⟨_,_⟩∣_∣  = λ p q r -> ⟨ q , p ⟩∣ sym r ∣
  ; comm      = sym comm
  ; ⟨⟩-inj    = λ r -> swap (⟨⟩-inj r)
  ; universal = λ r s -> universal s r
  } where open Pullback p

module _ {A B C : Obj} {f : A ⇒ C} {g : B ⇒ C} (p : Pullback f g) where
  module Pullback₁ = Pullback p
    renaming (Ob to Ob₁; π¹ to π¹₁; π² to π²₁; ⟨_,_⟩∣_∣ to ⟨_,_⟩∣_∣₁;
              comm to comm₁; ⟨⟩-inj to ⟨⟩-inj₁; universal to universal₁;
              ∘-η to ∘-η₁; π-inj to π-inj₁; π¹-⟨⟩ to π¹-⟨⟩₁; π²-⟨⟩ to π²-⟨⟩₁)

  module Pullback₂ = Pullback p
    renaming (Ob to Ob₂; π¹ to π¹₂; π² to π²₂; ⟨_,_⟩∣_∣ to ⟨_,_⟩∣_∣₂;
              comm to comm₂; ⟨⟩-inj to ⟨⟩-inj₂; universal to universal₂;
              ∘-η to ∘-η₂; π-inj to π-inj₂; π¹-⟨⟩ to π¹-⟨⟩₂; π²-⟨⟩ to π²-⟨⟩₂)

Pullbacks = ∀ {A B C : Obj} {f : A ⇒ C} {g : B ⇒ C} -> Pullback f g
