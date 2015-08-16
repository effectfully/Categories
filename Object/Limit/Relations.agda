open import Categories.Category

module Categories.Object.Limit.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Object.Limit.Product   ℂ
open import Categories.Object.Limit.Equalizer ℂ
open import Categories.Object.Limit.Pullback  ℂ

open Category ℂ

module _ {A B C} {f : A ⇒ C} {g : B ⇒ C} (p : Pullback f g) where
  open Pullback p

  Pullback->Equalizer : Equalizer (f ∘ π¹) (g ∘ π²)
  Pullback->Equalizer = record
    { Ob        = Ob
    ; ι         = id
    ; ↙_⟨_⟩     = λ p r -> p
    ; comm      = ∘-resp-≈ʳ comm
    ; ↙-inj     = id′
    ; Object = flip right idˡ
    }

module _ {A B} (p : Product A B) where
  open Product p renaming (Object to ↑-univ) hiding (Ob)

  Product&Equalizer->Pullback : ∀ {C} {f : A ⇒ C} {g : B ⇒ C}
                              -> Equalizer (f ∘ π¹) (g ∘ π²) -> Pullback f g
  Product&Equalizer->Pullback {_} {f} {g} e = record
    { Ob        = Ob
    ; π¹        = π¹ ∘ ι
    ; π²        = π² ∘ ι
    ; _↘_⟨_⟩    = λ p q r -> ↙ (p ↑ q) ⟨ sym π¹-↑ ʳ⌈ r ⌉ʳ sym π²-↑ ⟩
    ; comm      = reassoc² comm
    ; ↘-inj     = ↑-inj ∘′ ↙-inj
    ; Object = λ r s -> ↙-univ (sym (↑-univ (reassocˡ r) (reassocˡ s)))
    } where open Equalizer e renaming (Object to ↙-univ)
