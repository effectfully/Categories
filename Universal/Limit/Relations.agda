open import Categories.Category

module Categories.Universal.Limit.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Universal.Limit.Product   ℂ
open import Categories.Universal.Limit.Equalizer ℂ
open import Categories.Universal.Limit.Pullback  ℂ

open Category ℂ

module _ {A B C} {f : A ⇒ C} {g : B ⇒ C} (p : Pullback f g) where
  open Pullback p

  Pullback->Product : Product A B
  Pullback->Product = record
    { Ob        = Ob
    ; π₁        = π₁
    ; π₂        = π₂
    ; _↑_       = _↘_
    ; ↑-inj     = ↘-inj
    ; universal = universal
    }

  Pullback->Equalizer : Equalizer (f ∘ π₁) (g ∘ π₂)
  Pullback->Equalizer = record
    { Ob        = Ob
    ; ι         = id
    ; ↙_        = id→
    ; comm      = ∘-resp-≈ comm refl
    ; ↙-inj     = id→
    ; universal = flip right idˡ
    }

module _ {A B} (p : Product A B) where
  open Product p renaming (universal to ↑-univ) hiding (Ob)

  Product&Equalizer->Pullback : ∀ {C} {f : A ⇒ C} {g : B ⇒ C}
                              -> Equalizer (f ∘ π₁) (g ∘ π₂) -> Pullback f g
  Product&Equalizer->Pullback {_} {f} {g} e = record
    { Ob        = Ob
    ; π₁        = π₁ ∘ ι
    ; π₂        = π₂ ∘ ι
    ; _↘_       = λ p q -> ↙ (p ↑ q)
    ; comm      = reassoc² comm
    ; ↘-inj     = ↑-inj ∘′ ↙-inj
    ; universal = λ r s -> ↙-univ (sym (↑-univ (reassocˡ r) (reassocˡ s)))
    } where open Equalizer e renaming (universal to ↙-univ)