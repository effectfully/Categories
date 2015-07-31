open import Categories.Category.Base

module Categories.Morphism.Relations {α β γ} (ℂ : Category α β γ) where

open import Data.Product

open import Categories.Morphism.Morphism

open IEqReasoningWith ℂ

Mono->Epi : ∀ {A B} {f : A ⇒ B} -> Mono ℂ f -> Epi (ℂ ᵒᵖ) f
Mono->Epi = id→

Epi->Mono : ∀ {A B} {f : A ⇒ B} -> Epi ℂ f -> Mono (ℂ ᵒᵖ) f
Epi->Mono = id→

Iso->Iso : ∀ {A B} {f : A ⇒ B} -> Iso ℂ f -> Iso (ℂ ᵒᵖ) f
Iso->Iso i = record
  { f⁻¹  = f⁻¹
  ; isoˡ = isoʳ
  ; isoʳ = isoˡ
  } where open Iso ℂ i

Iso->Mono&Epi : ∀ {A B} {f : A ⇒ B} -> Iso ℂ f -> Mono ℂ f × Epi ℂ f
Iso->Mono&Epi {f = f} i =
  ( λ {C g h} p ->
      begin
        g             ←⟨ idˡ                  ⟩
        id ∘ g        →⟨ ∘-resp-≈ʳ (sym isoʳ) ⟩
        (f⁻¹ ∘ f) ∘ g →⟨ assoc                ⟩
        f⁻¹ ∘ (f ∘ g) →⟨ ∘-resp-≈ˡ   p        ⟩
        f⁻¹ ∘ (f ∘ h) ←⟨ assoc                ⟩
        (f⁻¹ ∘ f) ∘ h →⟨ ∘-resp-≈ʳ isoʳ       ⟩
        id ∘ h        →⟨ idˡ                  ⟩
        h
      ∎
  )                     ,
  ( λ {C g h} p ->
      begin
        g             ←⟨ idʳ                  ⟩
        g ∘ id        →⟨ ∘-resp-≈ˡ (sym isoˡ) ⟩
        g ∘ (f ∘ f⁻¹) ←⟨ assoc                ⟩
        (g ∘ f) ∘ f⁻¹ →⟨ ∘-resp-≈ʳ p          ⟩
        (h ∘ f) ∘ f⁻¹ →⟨ assoc                ⟩
        h ∘ (f ∘ f⁻¹) →⟨ ∘-resp-≈ˡ isoˡ       ⟩
        h ∘ id        →⟨ idʳ                  ⟩
        h
      ∎
  )
  where open Iso ℂ i
