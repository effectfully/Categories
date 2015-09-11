module Categories.Categories.Agda where

open import Data.Empty
open import Data.Sum

open import Categories.Utilities.Product
open import Categories.Category
open import Categories.Functor
open import Categories.Categories.Fun

Sets : ∀ {α} -> Category (suc α) α α
Sets {α} = record
  { Obj      = Set α
  ; _⇒_      = λ A B -> A -> B
  ; setoid   = →-ISetoid₂
  ; id       = id′
  ; _∘_      = λ g f -> g ∘′ f
  ; idˡ      = λ _ -> prefl
  ; idʳ      = λ _ -> prefl
  ; assoc    = λ _ -> prefl
  ; ∘-resp-≈ = ∘′-resp-≡
  }

module _ {α} where
  open import Categories.Object (Sets {α})

  terminal : Terminal
  terminal = record
    { Ob        = Lift ⊤
    ; universal = λ _ -> prefl
    }

  binaryProducts : BinaryProducts
  binaryProducts {A} {B} = record
    { Ob        = A ×ₚ B
    ; π¹        = proj₁
    ; π²        = proj₂
    ; ⟨_,_⟩     = <_,_>
    ; ⟨⟩-inj    = λ p -> proj₁ ∘′ ,′-inj ∘′ p , proj₂ ∘′ ,′-inj ∘′ p
    ; universal = λ p q x -> cong₂ _,_ (psym (p x)) (psym (q x))
    }

  equalizers : Equalizers
  equalizers {f = f} {g = g} = record
    { Ob        = ∃ᵢ λ x -> f x ≡ g x
    ; ι         = iproj₁
    ; ⟨_⟩∣_∣    = λ p r x -> p x ,ᵢ r x
    ; comm      = iproj₂
    ; ⟨⟩-inj    = λ p x -> ,ᵢ-inj₁ (p x)
    ; universal = λ r x -> ∃ᵢ-η (r x)
    }

  pullbacks : Pullbacks
  pullbacks = Product&Equalizer->Pullback binaryProducts equalizers

  initial : Initial
  initial = record
    { Ob        = Lift ⊥
    ; ↜         = λ{ (lift ()) }
    ; universal = λ{ (lift ()) }
    }

  binaryCoproducts : BinaryCoproducts
  binaryCoproducts {A} {B} = record
    { Ob        = A ⊎ B
    ; ι¹        = inj₁
    ; ι²        = inj₂
    ; [_,_]     = [_,_]
    ; []-inj    = λ p -> p ∘′ inj₁ , p ∘′ inj₂
    ; universal = λ p q -> [ psym ∘′ p , psym ∘′ q ]
    }

ISets : ∀ {ι α} -> Set ι -> Category (ι ⊔ suc α) (ι ⊔ α) (ι ⊔ α)
ISets {ι} {α} I = record
  { Obj      = I -> Set α
  ; _⇒_      = λ A B -> ∀ {i} -> A i -> B i
  ; setoid   = comap∀ⁱˢ (λ f i -> f {i}) →-ISetoid₂
  ; id       = id′
  ; _∘_      = λ g f -> g ∘′ f
  ; idˡ      = λ _ -> prefl
  ; idʳ      = λ _ -> prefl
  ; assoc    = λ _ -> prefl
  ; ∘-resp-≈ = λ q p -> ∘′-resp-≡ q p
  }

Setoids : ∀ α β -> Category (suc (α ⊔ β)) (α ⊔ β) (α ⊔ β)
Setoids α β = record
  { Obj      = [ Setoid A β ∣ A ∈ Set α ]
  ; _⇒_      = λ Aˢ Bˢ -> reveal Aˢ ─> reveal Bˢ
  ; setoid   = ─>-ISetoid₂
  ; id       = idᵖⁱ
  ; _∘_      = _∘ᵖⁱ_
  ; idˡ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; idʳ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; assoc    = λ {Aˢ Bˢ Cˢ Dˢ h g f} r -> f-resp-≈ (h ∘ᵖⁱ g ∘ᵖⁱ f) r
  ; ∘-resp-≈ = λ q p r -> q (p r)
  } where open Π

ISetoids : ∀ {ι} α β -> Set ι -> Category (ι ⊔ suc (α ⊔ β)) (ι ⊔ α ⊔ β) (ι ⊔ α ⊔ β)
ISetoids α β I = record
  { Obj      = [ ISetoid A β ∣ A ∈ (I -> Set α) ]
  ; _⇒_      = λ Aˢ Bˢ -> ∀ {i} -> instⁱˢ i (reveal Aˢ) ─> instⁱˢ i (reveal Bˢ)
  ; setoid   = comap∀ⁱˢ (λ f i -> f {i}) ─>-ISetoid₂
  ; id       = idᵖⁱ
  ; _∘_      = λ g f -> g ∘ᵖⁱ f
  ; idˡ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; idʳ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; assoc    = λ {Aˢ Bˢ Cˢ Dˢ h g f} r -> f-resp-≈ (h ∘ᵖⁱ g ∘ᵖⁱ f) r
  ; ∘-resp-≈ = λ q p r -> q (p r)
  } where open Π

Presheaf : ∀ {α β α₁ β₁ γ₁} -> Category α₁ β₁ γ₁ -> Set _
Presheaf {α} {β} C = Contravariant C (Setoids α β)

Copresheaf : ∀ {α β α₁ β₁ γ₁} -> Category α₁ β₁ γ₁ -> Set _
Copresheaf {α} {β} C = Functor C (Setoids α β)

Profunctor : ∀ {α β α₁ α₂ β₁ β₂ γ₁ γ₂} -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Set _
Profunctor {α} {β} C₁ C₂ = Bifunctor (C₁ ᵒᵖ) C₂ (Setoids α β)

Presheaves : ∀ {α β α₁ β₁ γ₁} -> Category α₁ β₁ γ₁ -> Category _ _ _
Presheaves {α} {β} C = Fun (C ᵒᵖ) (Setoids α β)
