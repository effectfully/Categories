open import Categories.Category

module Categories.Universal.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Universal.Limit.Terminal
open import Categories.Universal.Limit.Product
open import Categories.Universal.Limit.Equalizer
open import Categories.Universal.Limit.Pullback
open import Categories.Universal.Colimit.Initial
open import Categories.Universal.Colimit.Coproduct
open import Categories.Universal.Colimit.Coequalizer
open import Categories.Universal.Colimit.Pushout

open Category ℂ

Terminal->Initial : ∀ {A} -> Terminal ℂ A -> Initial (ℂ ᵒᵖ) A
Terminal->Initial t = record
  { ↜         = ↝
  ; universal = universal
  } where open Terminal ℂ t

Initial->Terminal : ∀ {A} -> Initial ℂ A -> Terminal (ℂ ᵒᵖ) A
Initial->Terminal i = record
  { ↝         = ↜
  ; universal = universal
  } where open Initial ℂ i

Product->Coproduct : ∀ {A B} -> Product ℂ A B -> Coproduct (ℂ ᵒᵖ) A B
Product->Coproduct p = record
  { Ob        = Ob
  ; ι₁        = π₁
  ; ι₂        = π₂
  ; _↓_       = _↑_
  ; ↓-inj     = ↑-inj
  ; universal = universal
  } where open Product ℂ p

Coproduct->Product : ∀ {A B} -> Coproduct ℂ A B -> Product (ℂ ᵒᵖ) A B
Coproduct->Product p = record
  { Ob        = Ob
  ; π₁        = ι₁
  ; π₂        = ι₂
  ; _↑_       = _↓_
  ; ↑-inj     = ↓-inj
  ; universal = universal
  } where open Coproduct ℂ p

Pullback->Pushout : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} -> Pullback ℂ f g -> Pushout (ℂ ᵒᵖ) f g
Pullback->Pushout p = record
  { Ob        = Ob
  ; ι₁        = π₁
  ; ι₂        = π₂
  ; _↖_       = _↘_
  ; comm      = comm
  ; ↖-inj     = ↘-inj
  ; universal = universal
  } where open Pullback ℂ p

Pushout->Pullback : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} -> Pushout ℂ f g -> Pullback (ℂ ᵒᵖ) f g
Pushout->Pullback p = record
  { Ob        = Ob
  ; π₁        = ι₁
  ; π₂        = ι₂
  ; _↘_       = _↖_
  ; comm      = comm
  ; ↘-inj     = ↖-inj
  ; universal = universal
  } where open Pushout ℂ p

Equalizer->Coequalizer : ∀ {A B} {f g : A ⇒ B} -> Equalizer ℂ f g -> Coequalizer (ℂ ᵒᵖ) f g
Equalizer->Coequalizer e = record
  { Ob        = Ob
  ; π         = ι
  ; _↗        = ↙_
  ; comm      = comm
  ; ↗-inj     = ↙-inj
  ; universal = universal
  } where open Equalizer ℂ e

Coequalizer->Equalizer : ∀ {A B} {f g : A ⇒ B} -> Coequalizer ℂ f g -> Equalizer (ℂ ᵒᵖ) f g
Coequalizer->Equalizer e = record
  { Ob        = Ob
  ; ι         = π
  ; ↙_        = _↗
  ; comm      = comm
  ; ↙-inj     = ↗-inj
  ; universal = universal
  } where open Coequalizer ℂ e