open import Categories.Category

module Categories.Universal.Limit.Pullback {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open import Categories.Morphism.Morphism ℂ

open IEqReasoningWith ℂ

record Pullback {A B C : Obj} (f : A ⇒ C) (g : B ⇒ C) : Set (α ⊔ β ⊔ γ) where
  infixr 5 _↘_

  field
    Ob  : Obj
    π₁  : Ob ⇒ A
    π₂  : Ob ⇒ B   
    _↘_ : ∀ {D} -> D ⇒ A -> D ⇒ B -> D ⇒ Ob

    comm     : f ∘ π₁ ≈ g ∘ π₂
    ↘-inj    : ∀ {D} {p₁ p₂ : D ⇒ A} {q₁ q₂ : D ⇒ B}
             -> p₁ ↘ q₁ ≈ p₂ ↘ q₂ -> p₁ ≈ p₂ × q₁ ≈ q₂
    universal : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} {u : D ⇒ Ob}
              -> π₁ ∘ u ≈ p -> π₂ ∘ u ≈ q -> p ↘ q ≈ u

  η : π₁ ↘ π₂ ≈ id
  η = universal idʳ idʳ

  ∘-η : ∀ {D} {u : D ⇒ Ob} -> π₁ ∘ u ↘ π₂ ∘ u ≈ u
  ∘-η = universal refl refl

  π-inj : ∀ {D} {p : D ⇒ Ob} {q : D ⇒ Ob}
        -> π₁ ∘ p ≈ π₁ ∘ q -> π₂ ∘ p ≈ π₂ ∘ q -> p ≈ q
  π-inj {_} {p} {q} r s =
    begin
      p               ←⟨ universal r s ⟩
      π₁ ∘ q ↘ π₂ ∘ q →⟨ ∘-η           ⟩
      q
    ∎

  π₁-↘ : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} -> π₁ ∘ (p ↘ q) ≈ p
  π₁-↘ = proj₁ (↘-inj ∘-η)

  π₂-↘ : ∀ {D} {p : D ⇒ A} {q : D ⇒ B} -> π₂ ∘ (p ↘ q) ≈ q
  π₂-↘ = proj₂ (↘-inj ∘-η)

  ↑-resp-≈ : ∀ {D} {p₁ p₂ : D ⇒ A} {q₁ q₂ : D ⇒ B}
           -> p₁ ≈ p₂ -> q₁ ≈ q₂ -> p₁ ↘ q₁ ≈ p₂ ↘ q₂
  ↑-resp-≈ r s = universal (left π₁-↘ r) (left π₂-↘ s)

  ↘-∘ : ∀ {D E} {r : D ⇒ E} {p : E ⇒ A} {q : E ⇒ B} -> (p ∘ r) ↘ (q ∘ r) ≈ (p ↘ q) ∘ r 
  ↘-∘ = universal (∘ˡ-resp-≈ʳ π₁-↘) (∘ˡ-resp-≈ʳ π₂-↘)

  π₁-Mono : Mono g -> Mono π₁
  π₁-Mono mono = λ r -> π-inj r (mono (∘²-resp-≈ʳ comm ⟨ ∘-resp-≈ˡ r ⟩ ∘²-resp-≈ʳ comm))

flip-Product : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} -> Pullback f g -> Pullback g f
flip-Product p = record
  { Ob        = Ob
  ; π₁        = π₂
  ; π₂        = π₁
  ; _↘_       = flip _↘_
  ; comm      = sym comm
  ; ↘-inj     = λ r -> swap (↘-inj r)
  ; universal = flip universal
  } where open Pullback p

-- flip-Product-≅ : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} -> {!_≃_!} -- Pullback f g ≃ Pullback g f
-- flip-Product-≅ = {!!}

glue : ∀ {A B C D} {h : C ⇒ A} {f : A ⇒ D} {g : B ⇒ D}
     -> (pᵣ : Pullback f g)
     -> let open Pullback pᵣ in
        Pullback h π₁
     -> Pullback (f ∘ h) g
glue {h = h} {f} {g} pᵣ pₗ = record
  { Ob        = pₗ.Ob
  ; π₁        = pₗ.π₁
  ; π₂        = pᵣ.π₂ ∘ pₗ.π₂
  ; _↘_       = λ p q -> p pₗ.↘ h ∘ p pᵣ.↘ q
  ; comm      =
      begin
        (f ∘ h) ∘ pₗ.π₁     →⟨ assoc             ⟩
        f ∘ h ∘ pₗ.π₁       →⟨ ∘-resp-≈ˡ pₗ.comm ⟩
        f ∘ pᵣ.π₁ ∘ pₗ.π₂   ←⟨ assoc             ⟩
        (f ∘ pᵣ.π₁) ∘ pₗ.π₂ →⟨ ∘-resp-≈ʳ pᵣ.comm ⟩
        (g ∘ pᵣ.π₂) ∘ pₗ.π₂ →⟨ assoc             ⟩
        g ∘ pᵣ.π₂ ∘ pₗ.π₂
      ∎
  ; ↘-inj     = λ {_ p₁ p₂ q₁ q₂} r -> case pₗ.↘-inj r of
      λ{ (s₁ , s₂) -> s₁ , proj₂ (pᵣ.↘-inj s₂) }
  ; universal = λ r s -> pₗ.universal r (sym (pᵣ.universal (∘²-resp-≈ʳ (sym pₗ.comm) ⋯ ∘-resp-≈ˡ r)
                                                           (reassocˡ s)))
  } where module pᵣ = Pullback pᵣ; module pₗ = Pullback pₗ

unglue : ∀ {A B C D} {h : C ⇒ A} {f : A ⇒ D} {g : B ⇒ D}
       -> (pᵣ : Pullback f g)
       -> let open Pullback pᵣ in
          (m : Mono π₂)
       -> Pullback (f ∘ h) g
       -> Pullback h π₁
unglue {h = h} {f} {g} pᵣ mono pₗᵣ = record
  { Ob        = pₗᵣ.Ob
  ; π₁        = pₗᵣ.π₁
  ; π₂        = h ∘ pₗᵣ.π₁ pᵣ.↘ pₗᵣ.π₂
  ; _↘_       = λ p q -> p pₗᵣ.↘ pᵣ.π₂ ∘ q
  ; comm      = sym pᵣ.π₁-↘
  ; ↘-inj     = λ {_ p₁ p₂ q₁ q₂} r -> case pₗᵣ.↘-inj r of λ{ (s₁ , s₂) -> s₁ , mono s₂ }
  ; universal = λ r s -> pₗᵣ.universal r (∘-resp-≈ʳ (sym pᵣ.π₂-↘) ⋯ ∘ˡ-resp-≈ˡ s)
  } where module pᵣ = Pullback pᵣ; module pₗᵣ = Pullback pₗᵣ
