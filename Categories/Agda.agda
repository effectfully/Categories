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
  } where
      ∘′-resp-≡ : ∀ {α} {A B C : Set α} {g₁ g₂ : B -> C} {f₁ f₂ : A -> B}
                -> (∀ y -> g₁ y ≡ g₂ y) -> (∀ x -> f₁ x ≡ f₂ x) -> ∀ x -> g₁ (f₁ x) ≡ g₂ (f₂ x)
      ∘′-resp-≡ q p x rewrite p x = q _

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

Setoids : ∀ {α γ} -> Category (suc (α ⊔ γ)) (α ⊔ γ) (α ⊔ γ)
Setoids {α} {γ} = record
  { Obj      = [ Setoid A γ ∣ A ∈ Set α ]
  ; _⇒_      = λ Aˢ Bˢ -> reveal Aˢ ─> reveal Bˢ
  ; setoid   = ─>-ISetoid₂
  ; id       = idˢ
  ; _∘_      = _∘ˢ_
  ; idˡ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; idʳ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; assoc    = λ {Aˢ Bˢ Cˢ Dˢ h g f} r -> f-resp-≈ (h ∘ˢ g ∘ˢ f) r
  ; ∘-resp-≈ = λ q p r -> q (p r)
  } where open Π

ISetoids : ∀ {ι α γ} -> Set ι -> Category (ι ⊔ suc (α ⊔ γ)) (ι ⊔ α ⊔ γ) (ι ⊔ α ⊔ γ)
ISetoids {ι} {α} {γ} I = record
  { Obj      = [ ISetoid A γ ∣ A ∈ (I -> Set α) ]
  ; _⇒_      = λ Aˢ Bˢ -> ∀ {i} -> inst (reveal Aˢ) i ─> inst (reveal Bˢ) i
  ; setoid   = comap∀ⁱˢ (λ f i -> f {i}) ─>-ISetoid₂
  ; id       = idˢ
  ; _∘_      = λ g f -> g ∘ˢ f
  ; idˡ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; idʳ      = λ {Aˢ Bˢ f}           r -> f-resp-≈ f r
  ; assoc    = λ {Aˢ Bˢ Cˢ Dˢ h g f} r -> f-resp-≈ (h ∘ˢ g ∘ˢ f) r
  ; ∘-resp-≈ = λ q p r -> q (p r)
  } where open ISetoid using (inst); open Π

Presheaf : ∀ {α γ α₁ β₁ γ₁} -> Category α₁ β₁ γ₁ -> Set _
Presheaf {α} {γ} C = Contravariant C (Setoids {α} {γ})

Copresheaf : ∀ {α γ α₁ β₁ γ₁} -> Category α₁ β₁ γ₁ -> Set _
Copresheaf {α} {γ} C = Functor C (Setoids {α} {γ})

Profunctor : ∀ {α γ α₁ α₂ β₁ β₂ γ₁ γ₂} -> Category α₁ β₁ γ₁ -> Category α₂ β₂ γ₂ -> Set _
Profunctor {α} {γ} C₁ C₂ = Bifunctor (C₁ ᵒᵖ) C₂ (Setoids {α} {γ})

Presheaves : ∀ {α γ α₁ β₁ γ₁} -> Category α₁ β₁ γ₁ -> Category _ _ _
Presheaves {α} {γ} C = Fun (C ᵒᵖ) (Setoids {α} {γ})
