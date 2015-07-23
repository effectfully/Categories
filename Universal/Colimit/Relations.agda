open import Categories.Category

module Categories.Universal.Colimit.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Universal.Colimit.Coproduct   ℂ
open import Categories.Universal.Colimit.Coequalizer ℂ
open import Categories.Universal.Colimit.Pushout     ℂ

open Category ℂ
open IndexedEqReasoningFrom ℂ

module _ {A B C} {f : C ⇒ A} {g : C ⇒ B} (p : Pushout f g) where
  open Pushout p

  Pushout->Coproduct : Coproduct A B
  Pushout->Coproduct = record
    { Ob        = Ob
    ; ι₁        = ι₁
    ; ι₂        = ι₂
    ; _↓_       = _↖_
    ; ↓-inj     = ↖-inj
    ; universal = universal
    }

  Pushout->Equalizer : Coequalizer (ι₁ ∘ f) (ι₂ ∘ g)
  Pushout->Equalizer = record
    { Ob        = Ob
    ; π         = id
    ; _↗        = id→
    ; comm      = ∘-resp-≈ irefl comm
    ; ↗-inj     = id→
    ; universal = λ r -> itrans (isym r) idʳ
    }

module _ {A B} (p : Coproduct A B) where
  open Coproduct p renaming (universal to ↓-univ) hiding (Ob)

  Product&Equalizer->Pullback : ∀ {C} {f : C ⇒ A} {g : C ⇒ B}
                              -> Coequalizer (ι₁ ∘ f) (ι₂ ∘ g) -> Pushout f g
  Product&Equalizer->Pullback {_} {f} {g} e = record
    { Ob        = Ob
    ; ι₁        = π ∘ ι₁
    ; ι₂        = π ∘ ι₂
    ; _↖_       = λ p q -> (p ↓ q) ↗
    ; comm      =
        begin
          (π ∘ ι₁) ∘ f →⟨ assoc _ ⟩
           π ∘ ι₁  ∘ f →⟨ comm    ⟩
           π ∘ ι₂  ∘ g ←⟨ assoc _ ⟩
          (π ∘ ι₂) ∘ g
        ∎
    ; ↖-inj     = ↓-inj ∘′ ↗-inj
    ; universal = λ r s -> ↗-univ (isym (↓-univ (itrans (assoc _) r)
                                                (itrans (assoc _) s)))
    } where open Coequalizer e renaming (universal to ↗-univ)
