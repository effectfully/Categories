-- This module doesn't typecheck because I can't open modules properly.

open import Categories.Category

module Categories.Object.Limit.Properties.Pullback {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism              ℂ
open import Categories.Object.Limit.Pullback ℂ

open Category ℂ

glue : ∀ {A B C D} {h : C ⇒ A} {f : A ⇒ D} {g : B ⇒ D}
     -> (p₂ : Pullback f g)
     -> let open Pullback p₂ in
        Pullback h π¹
     -> Pullback (f ∘ h) g
glue {h = h} {f} {g} p₂ p₁ = record
  { Ob        = Ob₁
  ; π¹        = π¹₁
  ; π²        = π²₂ ∘ π²₁
  ; ⟨_,_⟩∣_∣  = λ p q r -> ⟨ p , ⟨ h ∘ p , q ⟩∣ reassocˡ r ∣₂ ⟩∣ sym π¹-⟨⟩₂ ∣₁
  ; comm      = ∘ˡ-resp-≈ˡ comm₁ ⋯ ∘²-resp-≈ʳ comm₂
  ; ⟨⟩-inj    = λ {_ p₁ p₂ q₁ q₂} r -> case ⟨⟩-inj₁ r of
      λ{ (s₁ , s₂) -> s₁ , proj₂ (⟨⟩-inj₂ s₂) }
  ; universal = λ r s -> universal₁ r (sym (universal₂ (right (∘²-resp-≈ʳ comm₁) (∘-resp-≈ˡ r))
                                                       (reassocˡ s)))
  } where open Pullback₁ p₁; open Pullback₂ p₂

unglue : ∀ {A B C D} {h : C ⇒ A} {f : A ⇒ D} {g : B ⇒ D}
       -> (p₂ : Pullback f g)
       -> let open Pullback p₂ in
          (m : Mono π²)
       -> Pullback (f ∘ h) g
       -> Pullback h π¹
unglue {h = h} {f} {g} p₂ mono p₁ = record
  { Ob        = Ob₁
  ; π¹        = π¹₁
  ; π²        = ⟨ h ∘ π¹₁ , π²₁ ⟩∣ reassocˡ comm₁ ∣₂
  ; ⟨_,_⟩∣_∣  = λ p q r -> ⟨ p , π²₂ ∘ q ⟩∣ ∘ˡ-resp-≈ˡ r ⋯ ∘²-resp-≈ʳ comm₂ ∣₁
  ; comm      = sym π¹-⟨⟩₂
  ; ⟨⟩-inj    = λ {_ p₁ p₂ q₁ q₂} r -> case ⟨⟩-inj₁ r of λ{ (s₁ , s₂) -> s₁ , mono s₂ }
  ; universal = λ r s -> universal₁ r (right (∘-resp-≈ʳ π²-⟨⟩₂) (∘ˡ-resp-≈ˡ s))
  } where open Pullback₁ p₁; open Pullback₂ p₂