module Categories.Setoid.Function where

open import Level

open import Categories.Utilities.Prelude
open import Categories.Setoid.Setoid

infixr 9 _∘ˢ_

record Π {α β γ δ} {A : Set α} {B : A -> Set β}
         (Aˢ : Setoid A γ) (Bˢ : HSetoid B δ) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  open Setoid₁ Aˢ; open HSetoid₂ Bˢ

  field
    f·       : ∀ x -> B x
    f-resp-≈ : ∀ {x y} -> x ≈₁ y -> f· x ≈₂ f· y

module _ where
  open Π
  infixr 5 _⟨$⟩_
  _⟨$⟩_ = f·

module _ {α β γ δ} {A : Set α} {B : A -> Set β}
         {Aˢ : Setoid A γ} {Bˢ : HSetoid B δ} (f : Π Aˢ Bˢ) where
  module Π₁ where
    open Π f renaming (f· to f·₁; f-resp-≈ to f-resp-≈₁) public

  module Π₂ where
    open Π f renaming (f· to f·₂; f-resp-≈ to f-resp-≈₂) public

_─>_ : ∀ {α β γ δ} {A : Set α} {B : Set β} -> Setoid A γ -> Setoid B δ -> Set (α ⊔ β ⊔ γ ⊔ δ)
Aˢ ─> Bˢ = Π Aˢ hBˢ
  where open Indexed Bˢ renaming (hsetoid to hBˢ)

idˢ : ∀ {α γ} {A : Set α} {Aˢ : Setoid A γ} -> Aˢ ─> Aˢ
idˢ = record
  { f·       = id′
  ; f-resp-≈ = id′
  }

_∘ˢ_ : ∀ {α β γ δ ε ζ} {A : Set α} {B : Set β} {C : Set γ}
         {Aˢ : Setoid A δ} {Bˢ : Setoid B ε} {Cˢ : Setoid C ζ}
     -> Bˢ ─> Cˢ -> Aˢ ─> Bˢ -> Aˢ ─> Cˢ
g ∘ˢ f = record
  { f·       = f·₂ ∘′ f·₁
  ; f-resp-≈ = f-resp-≈₂ ∘′ f-resp-≈₁
  } where open Π₁ f; open Π₂ g

_≗_ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {Aˢ : Setoid A γ} {Bˢ : HSetoid B δ}
    -> Π Aˢ Bˢ -> Π Aˢ Bˢ -> Set (α ⊔ γ ⊔ δ)
_≗_ {Aˢ = Aˢ} {Bˢ = Bˢ} f g = ∀ {x y} -> x ≈₁ y -> f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  where open Setoid₁ Aˢ; open HSetoid₂ Bˢ

Injective : ∀ {α β γ δ} {A : Set α} {B : Set β} {Aˢ : Setoid A γ} {Bˢ : Setoid B δ}
          -> Aˢ ─> Bˢ -> Set (α ⊔ γ ⊔ δ)
Injective {Aˢ = Aˢ} {Bˢ = Bˢ} f = ∀ {x y} -> f ⟨$⟩ x ≈₂ f ⟨$⟩ y -> x ≈₁ y
  where open Setoid₁ Aˢ; open Setoid₂ Bˢ
