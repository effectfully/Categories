open import Categories.Category

module Categories.Object.Limit.Product {α β γ} (ℂ : Category α β γ) where

open Category ℂ

record Product A B : Set (α ⊔ β ⊔ γ) where
  field
    Ob    : Obj
    π¹    : Ob ⇒ A
    π²    : Ob ⇒ B
    ⟨_,_⟩ : ∀ {C} -> C ⇒ A -> C ⇒ B -> C ⇒ Ob

    ⟨⟩-inj  : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
            -> ⟨ f₁ , g₁ ⟩ ≈ ⟨ f₂ , g₂ ⟩ -> f₁ ≈ f₂ ×ₚ g₁ ≈ g₂
    ⟨⟩-univ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} {u : C ⇒ Ob}
            -> π¹ ∘ u ≈ f -> π² ∘ u ≈ g -> ⟨ f , g ⟩ ≈ u

  ⟨⟩-η : ⟨ π¹ , π² ⟩ ≈ id
  ⟨⟩-η = ⟨⟩-univ idʳ idʳ

  ⟨⟩-∘-η : ∀ {C} {u : C ⇒ Ob} -> ⟨ π¹ ∘ u , π² ∘ u ⟩ ≈ u
  ⟨⟩-∘-η = ⟨⟩-univ refl refl

  π¹-⟨⟩ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π¹ ∘ ⟨ f , g ⟩ ≈ f
  π¹-⟨⟩ = proj₁ (⟨⟩-inj ⟨⟩-∘-η)

  π²-⟨⟩ : ∀ {C} {f : C ⇒ A} {g : C ⇒ B} -> π² ∘ ⟨ f , g ⟩ ≈ g
  π²-⟨⟩ = proj₂ (⟨⟩-inj ⟨⟩-∘-η)
  
  ⟨⟩-∘ : ∀ {C D} {f : D ⇒ A} {g : D ⇒ B} {h : C ⇒ D} -> ⟨ f ∘ h , g ∘ h ⟩ ≈ ⟨ f , g ⟩ ∘ h
  ⟨⟩-∘ = ⟨⟩-univ (∘ˡ-resp-≈ʳ π¹-⟨⟩) (∘ˡ-resp-≈ʳ π²-⟨⟩)

  ⟨⟩-resp-≈ : ∀ {C} {f₁ f₂ : C ⇒ A} {g₁ g₂ : C ⇒ B}
            -> f₁ ≈ f₂ -> g₁ ≈ g₂ -> ⟨ f₁ , g₁ ⟩ ≈ ⟨ f₂ , g₂ ⟩
  ⟨⟩-resp-≈ p q = ⟨⟩-univ (left π¹-⟨⟩ p) (left π²-⟨⟩ q)

BinaryProducts = ∀ A B -> Product A B

module ProductTools ([_×_] : BinaryProducts) where
  infixr 7 _×_

  open module ImplicitProduct {A} {B} = Product [ A × B ] hiding (Ob) public

  _×_ : Obj -> Obj -> Obj
  A × B = Product.Ob [ A × B ]

  pmap : ∀ {A B C D} -> A ⇒ C -> B ⇒ D -> A × B ⇒ C × D
  pmap f g = ⟨ f ∘ π¹ , g ∘ π² ⟩

  pfirst : ∀ {A B C} -> A ⇒ C -> A × B ⇒ C × B
  pfirst f = pmap f id

  psecond : ∀ {A B D} -> B ⇒ D -> A × B ⇒ A × D
  psecond g = pmap id g
