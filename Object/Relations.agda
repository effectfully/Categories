open import Categories.Category

module Categories.Object.Relations {α β γ} (ℂ : Category α β γ) where

open import Categories.Object.Limit.Terminal
open import Categories.Object.Limit.Product
open import Categories.Object.Limit.Equalizer
open import Categories.Object.Limit.Pullback
open import Categories.Object.Colimit.Initial
open import Categories.Object.Colimit.Coproduct
open import Categories.Object.Colimit.Coequalizer
open import Categories.Object.Colimit.Pushout

open Category ℂ

Terminal->Initial : Terminal ℂ -> Initial (ℂ ᵒᵖ)
Terminal->Initial t = record
  { Ob     = Ob
  ; ↜      = ↝
  ; ↜-univ = ↝-univ
  } where open Terminal ℂ t

Initial->Terminal : Initial ℂ -> Terminal (ℂ ᵒᵖ)
Initial->Terminal i = record
  { Ob     = Ob
  ; ↝      = ↜
  ; ↝-univ = ↜-univ
  } where open Initial ℂ i

Product->Coproduct : ∀ {A B} -> Product ℂ A B -> Coproduct (ℂ ᵒᵖ) A B
Product->Coproduct p = record
  { Ob      = Ob
  ; ι¹      = π¹
  ; ι²      = π²
  ; [_,_]   = ⟨_,_⟩
  ; []-inj  = ⟨⟩-inj
  ; []-univ = ⟨⟩-univ
  } where open Product ℂ p

Coproduct->Product : ∀ {A B} -> Coproduct ℂ A B -> Product (ℂ ᵒᵖ) A B
Coproduct->Product p = record
  { Ob      = Ob
  ; π¹      = ι¹
  ; π²      = ι²
  ; ⟨_,_⟩   = [_,_]
  ; ⟨⟩-inj  = []-inj
  ; ⟨⟩-univ = []-univ
  } where open Coproduct ℂ p

Equalizer->Coequalizer : ∀ {A B} {f g : A ⇒ B} -> Equalizer ℂ f g -> Coequalizer (ℂ ᵒᵖ) f g
Equalizer->Coequalizer e = record
  { Ob      = Ob
  ; π       = ι
  ; [_]∣_∣  = ⟨_⟩∣_∣
  ; π-comm  = ι-comm
  ; []-inj  = ⟨⟩-inj
  ; []-univ = ⟨⟩-univ
  } where open Equalizer ℂ e

Coequalizer->Equalizer : ∀ {A B} {f g : A ⇒ B} -> Coequalizer ℂ f g -> Equalizer (ℂ ᵒᵖ) f g
Coequalizer->Equalizer e = record
  { Ob      = Ob
  ; ι       = π
  ; ⟨_⟩∣_∣  = [_]∣_∣
  ; ι-comm  = π-comm
  ; ⟨⟩-inj  = []-inj
  ; ⟨⟩-univ = []-univ
  } where open Coequalizer ℂ e

Pullback->Pushout : ∀ {A B C} {f : A ⇒ C} {g : B ⇒ C} -> Pullback ℂ f g -> Pushout (ℂ ᵒᵖ) f g
Pullback->Pushout p = record
  { Ob       = Ob
  ; ι¹       = π¹
  ; ι²       = π²
  ; [_,_]∣_∣ = ⟨_,_⟩∣_∣
  ; ι-comm   = π-comm
  ; []-inj   = ⟨⟩-inj
  ; []-univ  = ⟨⟩-univ
  } where open Pullback ℂ p

Pushout->Pullback : ∀ {A B C} {f : C ⇒ A} {g : C ⇒ B} -> Pushout ℂ f g -> Pullback (ℂ ᵒᵖ) f g
Pushout->Pullback p = record
  { Ob       = Ob
  ; π¹       = ι¹
  ; π²       = ι²
  ; ⟨_,_⟩∣_∣ = [_,_]∣_∣
  ; π-comm   = ι-comm
  ; ⟨⟩-inj   = []-inj
  ; ⟨⟩-univ  = []-univ
  } where open Pushout ℂ p
