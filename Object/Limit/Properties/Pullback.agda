-- This module doesn't typecheck because I can't open the modules properly.

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
  { Ob       = Ob₁
  ; π¹       = π¹₁
  ; π²       = π²₂ ∘ π²₁
  ; ⟨_,_⟩∣_∣ = λ p q r -> ⟨ p , ⟨ h ∘ p , q ⟩∣ reassocˡ r ∣₂ ⟩∣ sym π¹-⟨⟩₂ ∣₁
  ; π-comm   = ∘ˡ-resp-≈ˡ π-comm₁ ⋯ ∘²-resp-≈ʳ π-comm₂
  ; ⟨⟩-inj   = λ {_ p₁ p₂ q₁ q₂} r -> case ⟨⟩-inj₁ r of λ{ (s₁ , s₂) -> s₁ , proj₂ (⟨⟩-inj₂ s₂) }
  ; ⟨⟩-univ  = λ r s -> ⟨⟩-univ₁ r (sym (⟨⟩-univ₂ (right (∘²-resp-≈ʳ π-comm₁) (∘-resp-≈ˡ r))
                                                  (reassocˡ s)))
  } where open Pullback₁ p₁; open Pullback₂ p₂

unglue : ∀ {A B C D} {h : C ⇒ A} {f : A ⇒ D} {g : B ⇒ D}
       -> (p₂ : Pullback f g)
       -> let open Pullback p₂ in
          (m : Mono π²)
       -> Pullback (f ∘ h) g
       -> Pullback h π¹
unglue {h = h} {f} {g} p₂ mono p₁ = record
  { Ob       = Ob₁
  ; π¹       = π¹₁
  ; π²       = ⟨ h ∘ π¹₁ , π²₁ ⟩∣ reassocˡ π-comm₁ ∣₂
  ; ⟨_,_⟩∣_∣ = λ p q r -> ⟨ p , π²₂ ∘ q ⟩∣ ∘ˡ-resp-≈ˡ r ⋯ ∘²-resp-≈ʳ π-comm₂ ∣₁
  ; π-comm   = sym π¹-⟨⟩₂
  ; ⟨⟩-inj   = λ {_ p₁ p₂ q₁ q₂} r -> case ⟨⟩-inj₁ r of λ{ (s₁ , s₂) -> s₁ , mono s₂ }
  ; ⟨⟩-univ  = λ r s -> ⟨⟩-univ₁ r (right (∘-resp-≈ʳ π²-⟨⟩₂) (∘ˡ-resp-≈ˡ s))
  } where open Pullback₁ p₁; open Pullback₂ p₂
