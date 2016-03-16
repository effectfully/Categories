module Categories.Setoid.Function where

open import Categories.Utilities.Prelude
open import Categories.Setoid.Core

infixr 9 _∘ᵖⁱ_

record Π {α β γ δ} {A : Set α} {B : A -> Set β}
         (Aˢ : Setoid A γ) (Bˢ : HSetoid B δ) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  no-eta-equality
  
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
  module Π₁ = Π f renaming (f· to f·₁; f-resp-≈ to f-resp-≈₁)
  module Π₂ = Π f renaming (f· to f·₂; f-resp-≈ to f-resp-≈₂)

_─>_ : ∀ {α β γ δ} {A : Set α} {B : Set β} -> Setoid A γ -> Setoid B δ -> Set (α ⊔ β ⊔ γ ⊔ δ)
Aˢ ─> Bˢ = Π Aˢ hBˢ
  where open Indexed Bˢ renaming (hsetoid to hBˢ)

idᵖⁱ : ∀ {α γ} {A : Set α} {Aˢ : Setoid A γ} -> Aˢ ─> Aˢ
idᵖⁱ = record
  { f·       = id′
  ; f-resp-≈ = id′
  }

_∘ᵖⁱ_ : ∀ {α β γ δ ε ζ} {A : Set α} {B : Set β} {C : Set γ}
          {Aˢ : Setoid A δ} {Bˢ : Setoid B ε} {Cˢ : Setoid C ζ}
      -> Bˢ ─> Cˢ -> Aˢ ─> Bˢ -> Aˢ ─> Cˢ
g ∘ᵖⁱ f = record
  { f·       = f·₂ ∘′ f·₁
  ; f-resp-≈ = f-resp-≈₂ ∘′ f-resp-≈₁
  } where open Π₁ f; open Π₂ g

_×ᵖⁱ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂ δ₁ δ₂} {A₁ : Set α₁} {A₂ : Set α₂} {B₁ : Set β₁} {B₂ : Set β₂}
          {Aˢ₁ : Setoid A₁ γ₁} {Aˢ₂ : Setoid A₂ γ₂} {Bˢ₁ : Setoid B₁ δ₁} {Bˢ₂ : Setoid B₂ δ₂}
      -> Aˢ₁ ─> Bˢ₁ -> Aˢ₂ ─> Bˢ₂ -> (Aˢ₁ ×ˢ Aˢ₂) ─> (Bˢ₁ ×ˢ Bˢ₂)
f₁ ×ᵖⁱ f₂ = record
  { f·       = map f·₁ f·₂
  ; f-resp-≈ = map f-resp-≈₁ f-resp-≈₂
  } where open Π₁ f₁; open Π₂ f₂

_≗_ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {Aˢ : Setoid A γ} {Bˢ : HSetoid B δ}
    -> Π Aˢ Bˢ -> Π Aˢ Bˢ -> Set (α ⊔ γ ⊔ δ)
_≗_ {Aˢ = Aˢ} {Bˢ = Bˢ} f g = ∀ {x y} -> x ≈₁ y -> f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  where open Setoid₁ Aˢ; open HSetoid₂ Bˢ

Injective : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {Aˢ : Setoid A γ} {Bˢ : HSetoid B δ}
          -> Π Aˢ Bˢ -> Set (α ⊔ γ ⊔ δ)
Injective {Aˢ = Aˢ} {Bˢ = Bˢ} f = ∀ {x y} -> f ⟨$⟩ x ≈₂ f ⟨$⟩ y -> x ≈₁ y
  where open Setoid₁ Aˢ; open HSetoid₂ Bˢ

record HInjection {α β γ δ} {A : Set α} {B : A -> Set β}
                  (Aˢ : Setoid A γ) (Bˢ : HSetoid B δ) : Set (α ⊔ β ⊔ γ ⊔ δ) where
  no-eta-equality
  field
    π           : Π Aˢ Bˢ
    π-injective : Injective π

Injection : ∀ {α β γ δ} {A : Set α} {B : Set β}
          -> Setoid A γ -> Setoid B δ -> Set (α ⊔ β ⊔ γ ⊔ δ)
Injection Aˢ Bˢ = HInjection Aˢ hBˢ
  where open Indexed Bˢ renaming (hsetoid to hBˢ)

module _ {α β γ δ} {A : Set α} {B : A -> Set β} {Aˢ : Setoid A γ} {Bˢ : HSetoid B δ}
         (injection : HInjection Aˢ Bˢ) where
  module HInjection₁ = HInjection injection renaming (π to π₁; π-injective to π-injective₁)
  module HInjection₂ = HInjection injection renaming (π to π₂; π-injective to π-injective₂)

_×ⁱ_ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂ δ₁ δ₂} {A₁ : Set α₁} {A₂ : Set α₂} {B₁ : Set β₁} {B₂ : Set β₂}
         {Aˢ₁ : Setoid A₁ γ₁} {Aˢ₂ : Setoid A₂ γ₂} {Bˢ₁ : Setoid B₁ δ₁} {Bˢ₂ : Setoid B₂ δ₂}
     -> Injection Aˢ₁ Bˢ₁ -> Injection Aˢ₂ Bˢ₂ -> Injection (Aˢ₁ ×ˢ Aˢ₂) (Bˢ₁ ×ˢ Bˢ₂)
injection₁ ×ⁱ injection₂ = record
  { π           = π₁ ×ᵖⁱ π₂
  ; π-injective = map π-injective₁ π-injective₂
  } where open HInjection₁ injection₁; open HInjection₂ injection₂
