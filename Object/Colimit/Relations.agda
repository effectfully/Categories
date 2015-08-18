open import Categories.Category

module Categories.Object.Colimit.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Object.Colimit.Coproduct   ℂ
open import Categories.Object.Colimit.Coequalizer ℂ
open import Categories.Object.Colimit.Pushout     ℂ

open Category ℂ

module _ {A B C} {f : C ⇒ A} {g : C ⇒ B} (p : Pushout f g) where
  open Pushout p

  Pushout->Coequalizer : Coequalizer (ι¹ ∘ f) (ι² ∘ g)
  Pushout->Coequalizer = record
    { Ob        = Ob
    ; π         = id
    ; [_]∣_∣    = λ p r -> p
    ; comm      = ∘-resp-≈ˡ comm
    ; []-inj    = id′
    ; universal = flip right idʳ
    }

module _ {A B} (p : Coproduct A B) where
  open Coproduct p renaming ([]-inj to []-injₚ; universal to universalₚ) hiding (Ob)

  Coproduct&Coequalizer->Pushout : ∀ {C} {f : C ⇒ A} {g : C ⇒ B}
                                 -> Coequalizer (ι¹ ∘ f) (ι² ∘ g) -> Pushout f g
  Coproduct&Coequalizer->Pushout {_} {f} {g} e = record
    { Ob        = Ob
    ; ι¹        = π ∘ ι¹
    ; ι²        = π ∘ ι²
    -- This should be rewritten as (↓-ι¹ ʳ⌊ r ⌋ˡ ↓-ι²), but I'm tired with these aliases.
    ; [_,_]∣_∣  = λ p q r -> [ [ p , q ] ]∣ sym []-ι¹ ʳ⌈ r ⌉ˡ sym []-ι² ∣
    ; comm      = unreassoc² comm
    ; []-inj    = []-injₚ ∘′ []-injₑ
    ; universal = λ r s -> universalₑ (sym (universalₚ (unreassocˡ r) (unreassocˡ s)))
    } where open Coequalizer e renaming ([]-inj to []-injₑ; universal to universalₑ)
