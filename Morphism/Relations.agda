open import Categories.Category

module Categories.Morphism.Relations {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open import Categories.Morphism.Morphism

open IndexedEqReasoningWith ℂ

Mono->Epi : ∀ {A B} {f : A ⇒ B} -> Mono ℂ f -> Epi (ℂ ᵒᵖ) f
Mono->Epi m = record { epi = mono } where open Mono ℂ m

Epi->Mono : ∀ {A B} {f : A ⇒ B} -> Epi ℂ f -> Mono (ℂ ᵒᵖ) f
Epi->Mono e = record { mono = epi } where open Epi ℂ e

-- iso is iso

Iso->Mono&Epi : ∀ {A B} {f : A ⇒ B} -> Iso ℂ f -> Mono ℂ f × Epi ℂ f
Iso->Mono&Epi {f = f} i = record
  { mono = λ {C g h} p ->
      begin
        g             ←⟨ idˡ                        ⟩
        id ∘ g        →⟨ ∘-resp-≈ (isym isoʳ) irefl ⟩
        (f⁻¹ ∘ f) ∘ g →⟨ assoc                      ⟩
        f⁻¹ ∘ (f ∘ g) →⟨ ∘-resp-≈ irefl p           ⟩
        f⁻¹ ∘ (f ∘ h) ←⟨ assoc                      ⟩
        (f⁻¹ ∘ f) ∘ h →⟨ ∘-resp-≈ isoʳ irefl        ⟩
        id ∘ h        →⟨ idˡ                        ⟩
        h
      ∎
  }                     , record
  { epi = λ {C g h} p ->
      begin
        g             ←⟨ idʳ                        ⟩
        g ∘ id        →⟨ ∘-resp-≈ irefl (isym isoˡ) ⟩
        g ∘ (f ∘ f⁻¹) ←⟨ assoc                      ⟩
        (g ∘ f) ∘ f⁻¹ →⟨ ∘-resp-≈ p irefl           ⟩
        (h ∘ f) ∘ f⁻¹ →⟨ assoc                      ⟩
        h ∘ (f ∘ f⁻¹) →⟨ ∘-resp-≈ irefl isoˡ        ⟩
        h ∘ id        →⟨ idʳ                        ⟩
        h
      ∎
  }
  where open Iso ℂ i
