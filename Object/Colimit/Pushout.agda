open import Categories.Category

module Categories.Object.Colimit.Pushout {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Pushout {A B C} (f : C ⇒ A) (g : C ⇒ B) : Set (α ⊔ β ⊔ γ) where
  field
    Ob       : Obj
    ι¹       : A ⇒ Ob
    ι²       : B ⇒ Ob
    [_,_]∣_∣ : ∀ {D} -> (p : A ⇒ D) -> (q : B ⇒ D) -> .(p ∘ f ≈ q ∘ g) -> Ob ⇒ D

    .ι-comm  : ι¹ ∘ f ≈ ι² ∘ g
    .[]-inj  : ∀ {D} {p₁ p₂ : A ⇒ D} {q₁ q₂ : B ⇒ D} {r : p₁ ∘ f ≈ q₁ ∘ g} {s : p₂ ∘ f ≈ q₂ ∘ g}
             -> [ p₁ , q₁ ]∣ r ∣ ≈ [ p₂ , q₂ ]∣ s ∣ -> p₁ ≈ p₂ ×ₚ q₁ ≈ q₂
    .[]-univ : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {u : Ob ⇒ D}
             -> (r : u ∘ ι¹ ≈ p) -> (s : u ∘ ι² ≈ q) -> [ p , q ]∣ r ⌈ ∘²-resp-≈ˡ ι-comm ⌉ˡ s ∣ ≈ u

  .η : [ ι¹ , ι² ]∣ _ ∣ ≈ id
  η = []-univ idˡ idˡ

  .∘-η : ∀ {D} {u : Ob ⇒ D} -> [ u ∘ ι¹ , u ∘ ι² ]∣ _ ∣ ≈ u
  ∘-η = []-univ refl refl

  .[]-ι¹ : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {r : p ∘ f ≈ q ∘ g}
         -> [ p , q ]∣ r ∣ ∘ ι¹ ≈ p
  []-ι¹ = proj₁ ([]-inj ∘-η)

  .[]-ι² : ∀ {D} {p : A ⇒ D} {q : B ⇒ D} {r : p ∘ f ≈ q ∘ g}
         -> [ p , q ]∣ r ∣ ∘ ι² ≈ q
  []-ι² = proj₂ ([]-inj ∘-η)

  .∘-[] : ∀ {D E} {p : A ⇒ D} {q : B ⇒ D} {r : D ⇒ E} {s : p ∘ f ≈ q ∘ g}
        -> [ r ∘ p , r ∘ q ]∣ _ ∣ ≈ r ∘ [ p , q ]∣ s ∣
  ∘-[] = []-univ (∘ˡ-resp-≈ˡ []-ι¹) (∘ˡ-resp-≈ˡ []-ι²)

  .[]-resp-≈ : ∀ {D} {p₁ p₂ : A ⇒ D} {q₁ q₂ : B ⇒ D} {r : p₁ ∘ f ≈ q₁ ∘ g}
             -> (s : p₁ ≈ p₂) -> (t : q₁ ≈ q₂) -> [ p₁ , q₁ ]∣ r ∣ ≈ [ p₂ , q₂ ]∣ s ⌈ r ⌉ˡ t ∣ 
  []-resp-≈ p q = []-univ (left []-ι¹ p) (left []-ι² q)

Pushouts = ∀ {A B C} -> (f : C ⇒ A) -> (g : C ⇒ B) -> Pushout f g
