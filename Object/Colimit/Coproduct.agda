open import Categories.Category

module Categories.Object.Colimit.Coproduct {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Coproduct (A B : Obj) : Set (α ⊔ β ⊔ γ) where
  field
    Ob    : Obj
    ι¹    : A ⇒ Ob
    ι²    : B ⇒ Ob
    [_,_] : ∀ {C} -> A ⇒ C -> B ⇒ C -> Ob ⇒ C

    []-inj    : ∀ {C} {f₁ f₂ : A ⇒ C} {g₁ g₂ : B ⇒ C}
              -> [ f₁ , g₁ ] ≈ [ f₂ , g₂ ] -> f₁ ≈ f₂ ×ₚ g₁ ≈ g₂
    universal : ∀ {C} {f : A ⇒ C} {g : B ⇒ C} {u : Ob ⇒ C}
              -> u ∘ ι¹ ≈ f -> u ∘ ι² ≈ g -> [ f , g ] ≈ u

  η : [ ι¹ , ι² ] ≈ id
  η = universal idˡ idˡ

  ∘-η : ∀ {C} {u : Ob ⇒ C} -> [ u ∘ ι¹ , u ∘ ι² ] ≈ u
  ∘-η = universal refl refl

  []-ι¹ : ∀ {C} {f : A ⇒ C} {g : B ⇒ C} -> [ f , g ] ∘ ι¹ ≈ f
  []-ι¹ = proj₁ ([]-inj ∘-η)

  []-ι² : ∀ {C} {f : A ⇒ C} {g : B ⇒ C} -> [ f , g ] ∘ ι² ≈ g
  []-ι² = proj₂ ([]-inj ∘-η)

  ∘-[] : ∀ {C D} {f : A ⇒ C} {g : B ⇒ C} {h : C ⇒ D} -> [ h ∘ f , h ∘ g ] ≈ h ∘ [ f , g ]
  ∘-[] = universal (∘ˡ-resp-≈ˡ []-ι¹) (∘ˡ-resp-≈ˡ []-ι²)

  []-resp-≈ : ∀ {C} {f₁ f₂ : A ⇒ C} {g₁ g₂ : B ⇒ C}
            -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> [ f₁ , g₁ ] ≈ [ f₂ , g₂ ]
  []-resp-≈ p q = universal (left []-ι¹ p) (left []-ι² q)

BinaryCoproducts = ∀ {A B} -> Coproduct A B
