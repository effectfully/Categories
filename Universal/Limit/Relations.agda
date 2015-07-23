open import Categories.Category

module Categories.Universal.Limit.Relations {α β γ} (C : Category α β γ) where

open import Categories.Universal.Limit.Product   C
open import Categories.Universal.Limit.Equalizer C
open import Categories.Universal.Limit.Pullback  C

open Category C
open IndexedEqReasoningFrom C

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
    ; comm      = ∘-resp-≈ comm irefl
    ; ↙-inj     = id→
    ; universal = λ r -> isym (itrans (isym idˡ) r)
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
    ; comm      =
        begin
           f ∘ π₁  ∘ ι ←⟨ assoc _ ⟩
          (f ∘ π₁) ∘ ι →⟨ comm    ⟩
          (g ∘ π₂) ∘ ι →⟨ assoc _ ⟩
           g ∘ π₂  ∘ ι
        ∎
    ; ↘-inj     = ↑-inj ∘′ ↙-inj
    ; universal = λ r s -> ↙-univ (isym (↑-univ (itrans (isym (assoc _)) r)
                                                (itrans (isym (assoc _)) s)))
    } where open Equalizer e renaming (universal to ↙-univ)
