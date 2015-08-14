module Categories.Category.Category where

open import Categories.Utilities.Prelude public
open import Categories.Setoid public

module Category-Module where
  record Category α β γ : Set (suc (α ⊔ β ⊔ γ)) where
    infix  3 _⇒_
    infixr 9 _∘_
  
    field
      Obj    : Set α
      _⇒_    : Obj -> Obj -> Set β
      setoid : ISetoid₂ _⇒_ γ
      id     : ∀ {A}     -> A ⇒ A
      _∘_    : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    open ISetoid setoid

    field
      idˡ      : ∀ {A B} {f : A ⇒ B} -> id ∘ f ≈ f
      idʳ      : ∀ {A B} {f : A ⇒ B} -> f ∘ id ≈ f
      assoc    : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B}
               -> (h ∘ g) ∘ f ≈ h ∘ g ∘ f
      ∘-resp-≈ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
               -> g₁ ≈ g₂ -> f₁ ≈ f₂ -> g₁ ∘ f₁ ≈ g₂ ∘ f₂

    module Tools where
      ∘-resp-≈ˡ : ∀ {A B C} {g : B ⇒ C} {f₁ f₂ : A ⇒ B} -> f₁ ≈ f₂ -> g ∘ f₁ ≈ g ∘ f₂
      ∘-resp-≈ˡ p = ∘-resp-≈ refl p

      ∘-resp-≈ʳ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f : A ⇒ B} -> g₁ ≈ g₂ -> g₁ ∘ f ≈ g₂ ∘ f
      ∘-resp-≈ʳ p = ∘-resp-≈ p refl

      ∘-resp-≈ʳˡ : ∀ {A B C D} {h : C ⇒ D} {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
                 -> g₁ ≈ g₂ -> h ∘ g₁ ∘ f ≈ h ∘ g₂ ∘ f
      ∘-resp-≈ʳˡ = ∘-resp-≈ˡ ∘′ ∘-resp-≈ʳ

      ∘-resp-≈ˡʳ : ∀ {A B C D} {h : C ⇒ D} {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
                 -> g₁ ≈ g₂ -> (h ∘ g₁) ∘ f ≈ (h ∘ g₂) ∘ f
      ∘-resp-≈ˡʳ = ∘-resp-≈ʳ ∘′ ∘-resp-≈ˡ

      reassocˡ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
               -> (h ∘ g) ∘ f ≈ i -> h ∘ g ∘ f ≈ i
      reassocˡ = right assoc

      reassocʳ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
               -> i ≈ (h ∘ g) ∘ f -> i ≈ h ∘ g ∘ f
      reassocʳ = flip trans assoc

      reassoc² : ∀ {A B₁ B₂ C₁ C₂ D} {h₁ : C₁ ⇒ D} {h₂ : C₂ ⇒ D}
                   {g₁ : B₁ ⇒ C₁} {g₂ : B₂ ⇒ C₂} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
               -> (h₁ ∘ g₁) ∘ f₁ ≈ (h₂ ∘ g₂) ∘ f₂ -> h₁ ∘ g₁ ∘ f₁ ≈ h₂ ∘ g₂ ∘ f₂
      reassoc² = assoc ⌈_⌉ assoc

      unreassocˡ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
                 -> h ∘ g ∘ f ≈ i -> (h ∘ g) ∘ f ≈ i
      unreassocˡ = trans assoc

      unreassocʳ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
                 -> i ≈ h ∘ g ∘ f -> i ≈ (h ∘ g) ∘ f
      unreassocʳ = flip left assoc

      unreassoc² : ∀ {A B₁ B₂ C₁ C₂ D} {h₁ : C₁ ⇒ D} {h₂ : C₂ ⇒ D}
                     {g₁ : B₁ ⇒ C₁} {g₂ : B₂ ⇒ C₂} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
                 -> h₁ ∘ g₁ ∘ f₁ ≈ h₂ ∘ g₂ ∘ f₂ -> (h₁ ∘ g₁) ∘ f₁ ≈ (h₂ ∘ g₂) ∘ f₂
      unreassoc² = assoc ⌊_⌋ assoc

      ∘ˡ-resp-≈ˡ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : C ⇒ D} 
                 -> g ∘ f ≈ i -> (h ∘ g) ∘ f ≈ h ∘ i
      ∘ˡ-resp-≈ˡ = unreassocˡ ∘′ ∘-resp-≈ˡ

      ∘ʳ-resp-≈ˡ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : C ⇒ D} 
                 -> i ≈ g ∘ f -> h ∘ i ≈ (h ∘ g) ∘ f
      ∘ʳ-resp-≈ˡ = unreassocʳ ∘′ ∘-resp-≈ˡ

      ∘²-resp-≈ˡ : ∀ {A B₁ B₂ C D} {h : C ⇒ D} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
                     {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
                 -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> (h ∘ g₁) ∘ f₁ ≈ (h ∘ g₂) ∘ f₂
      ∘²-resp-≈ˡ = unreassoc² ∘′ ∘-resp-≈ˡ

      ∘ˡ-resp-≈ʳ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : D ⇒ A}
                 -> g ∘ f ≈ i -> g ∘ f ∘ h ≈ i ∘ h
      ∘ˡ-resp-≈ʳ = reassocˡ ∘′ ∘-resp-≈ʳ

      ∘ʳ-resp-≈ʳ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : D ⇒ A}
                 -> i ≈ g ∘ f -> i ∘ h ≈ g ∘ f ∘ h
      ∘ʳ-resp-≈ʳ = reassocʳ ∘′ ∘-resp-≈ʳ

      ∘²-resp-≈ʳ : ∀ {A B₁ B₂ C D} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
                     {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {h : D ⇒ A}
                 -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> g₁ ∘ f₁ ∘ h ≈ g₂ ∘ f₂ ∘ h
      ∘²-resp-≈ʳ = reassoc² ∘′ ∘-resp-≈ʳ

      _⌈_⌉ˡ_ : ∀ {A B₁ B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {g₁ g₁' : B₁ ⇒ C} {g₂ g₂' : B₂ ⇒ C}
             -> g₁ ≈ g₁' -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> g₂ ≈ g₂' -> g₁' ∘ f₁ ≈ g₂' ∘ f₂
      p ⌈ r ⌉ˡ q = ∘-resp-≈ʳ p ⌈ r ⌉ ∘-resp-≈ʳ q

      _ʳ⌈_⌉ˡ_ : ∀ {A B₁ B₁₁ B₂₁ B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
                  {g₁₁ : B₁ ⇒ B₁₁} {g₁₂ : B₁₁ ⇒ C} {g₂₁ : B₂ ⇒ B₂₁} {g₂₂ : B₂₁ ⇒ C}
              -> g₁ ≈ g₁₂ ∘ g₁₁
              -> g₁ ∘ f₁ ≈ g₂ ∘ f₂
              -> g₂ ≈ g₂₂ ∘ g₂₁
              -> g₁₂ ∘ g₁₁ ∘ f₁ ≈ g₂₂ ∘ g₂₁ ∘ f₂
      p ʳ⌈ r ⌉ˡ q = ∘ʳ-resp-≈ʳ p ⌈ r ⌉ ∘ʳ-resp-≈ʳ q

      _²⌈_⌉ˡ_ : ∀ {A B₁ B₁₁ B₁₁' B₂₁ B₂₁' B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
                  {g₁₁ : B₁ ⇒ B₁₁} {g₁₁' : B₁ ⇒ B₁₁'} {g₁₂ : B₁₁ ⇒ C} {g₁₂' : B₁₁' ⇒ C}
                  {g₂₁ : B₂ ⇒ B₂₁} {g₂₁' : B₂ ⇒ B₂₁'} {g₂₂ : B₂₁ ⇒ C} {g₂₂' : B₂₁' ⇒ C}
              -> g₁₂ ∘ g₁₁ ≈ g₁₂' ∘ g₁₁'
              -> g₁₂ ∘ g₁₁ ∘ f₁ ≈ g₂₂ ∘ g₂₁ ∘ f₂
              -> g₂₂ ∘ g₂₁ ≈ g₂₂' ∘ g₂₁'
              -> g₁₂' ∘ g₁₁' ∘ f₁ ≈ g₂₂' ∘ g₂₁' ∘ f₂
      p ²⌈ r ⌉ˡ q = ∘²-resp-≈ʳ p ⌈ r ⌉ ∘²-resp-≈ʳ q

      _⌈_⌉ʳ_ : ∀ {A B₁ B₂ C} {f₁ f₁' : A ⇒ B₁} {f₂ f₂' : A ⇒ B₂} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
             -> f₁ ≈ f₁' -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> f₂ ≈ f₂' -> g₁ ∘ f₁' ≈ g₂ ∘ f₂'
      p ⌈ r ⌉ʳ q = ∘-resp-≈ˡ p ⌈ r ⌉ ∘-resp-≈ˡ q

      _ʳ⌈_⌉ʳ_ : ∀ {A A₁₁ A₂₁ B₁ B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
                  {f₁₁ : A ⇒ A₁₁} {f₁₂ : A₁₁ ⇒ B₁} {f₂₁ : A ⇒ A₂₁} {f₂₂ : A₂₁ ⇒ B₂}
              -> f₁ ≈ f₁₂ ∘ f₁₁
              -> g₁ ∘ f₁ ≈ g₂ ∘ f₂
              -> f₂ ≈ f₂₂ ∘ f₂₁
              -> (g₁ ∘ f₁₂) ∘ f₁₁ ≈ (g₂ ∘ f₂₂) ∘ f₂₁
      p ʳ⌈ r ⌉ʳ q = ∘ʳ-resp-≈ˡ p ⌈ r ⌉ ∘ʳ-resp-≈ˡ q
open Category-Module renaming (module Category to Just-Category) public

module Category {α β γ} (C : Category α β γ) where
  open Just-Category C public; open ISetoid setoid public; open Tools public

_ᵒᵖ : ∀ {α β γ} -> Category α β γ -> Category α β γ
C ᵒᵖ = record 
  { _⇒_      = flip _⇒_
  ; setoid   = record
      { _≈_            = _≈_
      ; isIEquivalence = record
          { refl  = refl
          ; sym   = sym
          ; trans = trans
          }
      }
  ; id       = id
  ; _∘_      = flip _∘_
  ; idˡ      = idʳ
  ; idʳ      = idˡ
  ; assoc    = sym assoc
  ; ∘-resp-≈ = flip ∘-resp-≈
  } where open Category C

module _ {α β γ} (C : Category α β γ) where
  open Category C

  module ISetoidFrom      = ISetoid setoid
  module IEqReasoningFrom = IEqReasoning setoid

  module Just-Heterogeneous where
    open Just-Hetero setoid

    ∘-resp-≋ : ∀ {A A' B B' C C'} {g₁ : B ⇒ C} {g₂ : B' ⇒ C'} {f₁ : A ⇒ B} {f₂ : A' ⇒ B'}
             -> g₁ ≋ g₂ -> f₁ ≋ f₂ -> g₁ ∘ f₁ ≋ g₂ ∘ f₂
    ∘-resp-≋ (hetero g₁≈g₂) (hetero f₁≈f₂) = hetero (∘-resp-≈ g₁≈g₂ f₁≈f₂)

  module Heterogeneous where
    open Hetero setoid public; open Just-Heterogeneous public

  module MixedEqReasoningFrom where
    open Heterogeneous public; open MixedEqReasoning setoid public

module IEqReasoningWith {α β γ} (C : Category α β γ) where
  open Category C public; open IEqReasoning setoid public

module _ {α β γ} (C : Category α β γ) where
  module Category₁ where
    open Just-Category C renaming
      (Obj to Obj₁; _⇒_ to _⇒₁_; id to id₁; _∘_ to _∘₁_; setoid to setoid₁;
       idˡ to idˡ₁; idʳ to idʳ₁; assoc to assoc₁; ∘-resp-≈ to ∘-resp-≈₁;
       module Tools to Tools₁) public
    open Just-Heterogeneous C renaming (∘-resp-≋ to ∘-resp-≋₁) public
    open ISetoid₁ setoid₁ public
    private open module H = Just-Hetero setoid₁
                              renaming (hetero to hetero₁; homo to homo₁) using () public
    open HSetoid₁ H.hsetoid renaming (_≈₁_ to _≋₁_) public

  module Category₂ where
    open Just-Category C renaming
      (Obj to Obj₂; _⇒_ to _⇒₂_; id to id₂; _∘_ to _∘₂_; setoid to setoid₂;
       idˡ to idˡ₂; idʳ to idʳ₂; assoc to assoc₂; ∘-resp-≈ to ∘-resp-≈₂;
       module Tools to Tools₂) public
    open Just-Heterogeneous C renaming (∘-resp-≋ to ∘-resp-≋₂) public
    open ISetoid₂ setoid₂ public
    private open module H = Just-Hetero setoid₂
                              renaming (hetero to hetero₂; homo to homo₂) using () public
    open HSetoid₂ H.hsetoid renaming (_≈₂_ to _≋₂_) public

  module Category₃ where
    open Just-Category C renaming
      (Obj to Obj₃; _⇒_ to _⇒₃_; id to id₃; _∘_ to _∘₃_; setoid to setoid₃;
       idˡ to idˡ₃; idʳ to idʳ₃; assoc to assoc₃; ∘-resp-≈ to ∘-resp-≈₃;
       module Tools to Tools₃) public
    open Just-Heterogeneous C renaming (∘-resp-≋ to ∘-resp-≋₃) public
    open ISetoid₃ setoid₃ public
    private open module H = Just-Hetero setoid₃
                              renaming (hetero to hetero₃; homo to homo₃) using () public
    open HSetoid₃ H.hsetoid renaming (_≈₃_ to _≋₃_) public

module _ {α₁ α₂ β γ} {Obj₁ : Set α₁} (C : Category α₂ β γ) where
  open Category₂ C

  _ᶜ⟨$⟩_ : ∀ {β₁ β₂} {Obj-setoid₁ : Setoid Obj₁ β₁} {Obj-setoid₂ : Setoid Obj₂ β₂}
         -> (Obj-setoid₁ ─> Obj-setoid₂) -> Category α₁ β γ
  _ᶜ⟨$⟩_ f = record
    { Obj      = Obj₁
    ; _⇒_      = λ A B -> f ⟨$⟩ A ⇒₂ f ⟨$⟩ B
    ; setoid   = setoid₂ ˢ⟨$⟩ (f ×ʳ f)
    ; id       = id₂
    ; _∘_      = _∘₂_
    ; idˡ      = idˡ₂
    ; idʳ      = idʳ₂
    ; assoc    = assoc₂
    ; ∘-resp-≈ = ∘-resp-≈₂
    }

module _ where
  open Category

  arr-syntax  = _⇒_
  eq-syntax   = _≈_
  comp-syntax = _∘_
  heq-syntax  = Heterogeneous._≋_

  syntax arr-syntax  C A B = A [ C ]⇒ B
  syntax eq-syntax   C f g = f [ C ]≈ g
  syntax comp-syntax C f g = f [ C ]∘ g
  syntax heq-syntax  C f g = f [ C ]≋ g
