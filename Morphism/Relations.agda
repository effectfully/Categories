open import Categories.Category

module Categories.Morphism.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Morphism.Core

open IEqReasoningWith ℂ

Mono->Epi : ∀ {A B} {f : A ⇒ B} -> Mono ℂ f -> Epi (ℂ ᵒᵖ) f
Mono->Epi = id′

Epi->Mono : ∀ {A B} {f : A ⇒ B} -> Epi ℂ f -> Mono (ℂ ᵒᵖ) f
Epi->Mono = id′

Iso->Iso : ∀ {A B} {f : A ⇒ B} {f⁻¹ : B ⇒ A} -> Iso ℂ f f⁻¹ -> Iso (ℂ ᵒᵖ) f f⁻¹
Iso->Iso i = record
  { isoˡ = isoʳ
  ; isoʳ = isoˡ
  } where open Iso ℂ i

-- Iso->Mono&Epi : ∀ {A B} {f : A ⇒ B} -> Iso ℂ f -> Mono ℂ f ×ₚ Epi ℂ f
-- Iso->Mono&Epi {f = f} i =
--   ( λ {C g h} p ->
--       begin
--         g             ←⟨ idˡ                  ⟩
--         id ∘ g        →⟨ ∘-resp-≈ʳ (sym isoˡ) ⟩
--         (f⁻¹ ∘ f) ∘ g →⟨ assoc                ⟩
--         f⁻¹ ∘ (f ∘ g) →⟨ ∘-resp-≈ˡ   p        ⟩
--         f⁻¹ ∘ (f ∘ h) ←⟨ assoc                ⟩
--         (f⁻¹ ∘ f) ∘ h →⟨ ∘-resp-≈ʳ isoˡ       ⟩
--         id ∘ h        →⟨ idˡ                  ⟩
--         h
--       ∎
--   )                     ,
--   ( λ {C g h} p ->
--       begin
--         g             ←⟨ idʳ                  ⟩
--         g ∘ id        →⟨ ∘-resp-≈ˡ (sym isoʳ) ⟩
--         g ∘ (f ∘ f⁻¹) ←⟨ assoc                ⟩
--         (g ∘ f) ∘ f⁻¹ →⟨ ∘-resp-≈ʳ p          ⟩
--         (h ∘ f) ∘ f⁻¹ →⟨ assoc                ⟩
--         h ∘ (f ∘ f⁻¹) →⟨ ∘-resp-≈ˡ isoʳ       ⟩
--         h ∘ id        →⟨ idʳ                  ⟩
--         h
--       ∎
--   )
--   where open Iso ℂ i
