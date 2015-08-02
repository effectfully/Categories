open import Categories.Category

module Categories.Universal.Colimit.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Universal.Colimit.Coproduct   ℂ
open import Categories.Universal.Colimit.Coequalizer ℂ
open import Categories.Universal.Colimit.Pushout     ℂ

open Category ℂ

module _ {A B C} {f : C ⇒ A} {g : C ⇒ B} (p : Pushout f g) where
  open Pushout p

  Pushout->Coequalizer : Coequalizer (ι¹ ∘ f) (ι² ∘ g)
  Pushout->Coequalizer = record
    { Ob        = Ob
    ; π         = id
    ; _↗⟨_⟩     = λ p₁ r -> p₁
    ; comm      = ∘-resp-≈ˡ comm
    ; ↗-inj     = id→
    ; universal = flip right idʳ
    }

module _ {A B} (p : Coproduct A B) where
  open Coproduct p renaming (universal to ↓-univ) hiding (Ob)

  Coproduct&Coequalizer->Pushout : ∀ {C} {f : C ⇒ A} {g : C ⇒ B}
                                 -> Coequalizer (ι¹ ∘ f) (ι² ∘ g) -> Pushout f g
  Coproduct&Coequalizer->Pushout {_} {f} {g} e = record
    { Ob        = Ob
    ; ι¹        = π ∘ ι¹
    ; ι²        = π ∘ ι²
    -- This should be rewritten as (↓-ι¹ ʳ⌊ r ⌋ˡ ↓-ι²), but I'm tired with these aliases.
    ; _↖_⟨_⟩    = λ p q r -> (p ↓ q) ↗⟨ sym ↓-ι¹ ʳ⌈ r ⌉ˡ sym ↓-ι² ⟩
    ; comm      = unreassoc² comm
    ; ↖-inj     = ↓-inj ∘′ ↗-inj
    ; universal = λ r s -> ↗-univ (sym (↓-univ (unreassocˡ r) (unreassocˡ s)))
    } where open Coequalizer e renaming (universal to ↗-univ)
