module Categories.Categories.Mon where

open import Categories.Category
open import Categories.Functor

module Monoid-Module where
  record Monoid {α} (A : Set α) β : Set (α ⊔ suc β) where
    infix 5 _∙_

    field
      ε      : A
      _∙_    : A -> A -> A
      setoid : Setoid A β

    open Setoid setoid

    field
      idˡ      : ∀ {x} -> ε ∙ x ≈ x
      idʳ      : ∀ {x} -> x ∙ ε ≈ x
      assoc    : ∀ {x y z} -> (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      ∙-resp-≈ : ∀ {x₁ x₂ y₁ y₂} -> x₁ ≈ x₂ -> y₁ ≈ y₂ -> x₁ ∙ y₁ ≈ x₂ ∙ y₂
open Monoid-Module renaming (module Monoid to Just-Monoid) public

module Monoid {α β} {A : Set α} (M : Monoid A β) where
  open Just-Monoid M public; open Setoid setoid public

module _ {α β} {A : Set α} (M : Monoid A β) where
  module Monoid₁ where
    open Just-Monoid M
      renaming (ε to ε₁; _∙_ to _∙₁_; setoid to setoid₁;
                idˡ to idˡ₁; idʳ to idʳ₁; assoc to assoc₁; ∙-resp-≈ to ∙-resp-≈₁) public
    open Setoid₁ setoid₁ public

  module Monoid₂ where
    open Just-Monoid M
      renaming (ε to ε₂; _∙_ to _∙₂_; setoid to setoid₂;
                idˡ to idˡ₂; idʳ to idʳ₂; assoc to assoc₂; ∙-resp-≈ to ∙-resp-≈₂) public
    open Setoid₂ setoid₂ public

  module Monoid₃ where
    open Just-Monoid M
      renaming (ε to ε₃; _∙_ to _∙₃_; setoid to setoid₃;
                idˡ to idˡ₃; idʳ to idʳ₃; assoc to assoc₃; ∙-resp-≈ to ∙-resp-≈₃) public
    open Setoid₃ setoid₃ public

module EqReasoningFrom {α β} {A : Set α} (M : Monoid A β) where
  open Monoid M; open EqReasoning setoid public

record Homo {α₁ α₂ β₁ β₂} {A₁ : Set α₁} {A₂ : Set α₂} 
            (M₁ : Monoid A₁ β₁) (M₂ : Monoid A₂ β₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂) where
  open Monoid₁ M₁; open Monoid₂ M₂

  field
    f· : A₁ -> A₂

    f-ε      : f· ε₁ ≈₂ ε₂
    f-∙      : ∀ {x y} -> f· (x ∙₁ y) ≈₂ f· x ∙₂ f· y
    f-resp-≈ : ∀ {x y} -> x ≈₁ y -> f· x ≈₂ f· y

module _ {α₁ α₂ β₁ β₂} {A₁ : Set α₁} {A₂ : Set α₂}
         {M₁ : Monoid A₁ β₁} {M₂ : Monoid A₂ β₂} (H : Homo M₁ M₂) where
  module Homo₁ = Homo H renaming (f· to f·₁; f-ε to f-ε₁; f-∙ to f-∙₁; f-resp-≈ to f-resp-≈₁)

  module Homo₂ = Homo H renaming (f· to f·₂; f-ε to f-ε₂; f-∙ to f-∙₂; f-resp-≈ to f-resp-≈₂)

  module Homo₃ = Homo H renaming (f· to f·₃; f-ε to f-ε₃; f-∙ to f-∙₃; f-resp-≈ to f-resp-≈₃)

idʰ : ∀ {α β} {A : Set α} {M : Monoid A β} -> Homo M M
idʰ {M = M} = record
  { f·       = id′
  ; f-ε      = refl
  ; f-∙      = refl
  ; f-resp-≈ = id′
  } where open Monoid M

-- Can we derive this from the fact, that monoid homomorphisms are functors? Should we?
_∘ʰ_ : ∀ {α₁ α₂ α₃ β₁ β₂ β₃} {A₁ : Set α₁} {A₂ : Set α₂} {A₃ : Set α₃}
         {M₁ : Monoid A₁ β₁} {M₂ : Monoid A₂ β₂} {M₃ : Monoid A₃ β₃}
     -> Homo M₂ M₃ -> Homo M₁ M₂ -> Homo M₁ M₃
_∘ʰ_ {M₁ = M₁} {M₂ = M₂} {M₃ = M₃} H₂ H₁ = record
  { f·       = f·₂ ∘′ f·₁
  ; f-ε      =
      begin
        f·₂ (f·₁ ε₁) →⟨ f-resp-≈₂ f-ε₁ ⟩
        f·₂  ε₂      →⟨ f-ε₂           ⟩
        ε₃
      ∎
  ; f-∙      = λ {x y} ->
      begin
        f·₂ (f·₁ (x ∙₁ y))         →⟨ f-resp-≈₂ f-∙₁ ⟩
        f·₂ (f·₁ x ∙₂ f·₁ y)       →⟨ f-∙₂           ⟩
        f·₂ (f·₁ x) ∙₃ f·₂ (f·₁ y)
      ∎
  ; f-resp-≈ = f-resp-≈₂ ∘′ f-resp-≈₁
  } where open Homo₁ H₁; open Homo₂ H₂
          open Monoid₁ M₁; open Monoid₂ M₂; open Monoid₃ M₃; open EqReasoningFrom M₃

Homo-ISetoid₂ : ∀ {α₁ α₂ β₁ β₂} {A₁ : Set α₁} {A₂ : Set α₂}
              -> ISetoid₂ (Homo {β₁ = β₁} {β₂ = β₂} {A₁} {A₂}) (α₁ ⊔ β₂)
Homo-ISetoid₂ = record
  { _≈_            = λ{ {M₁ , M₂} H₁ H₂ -> let open Homo₁ H₁; open Homo₂ H₂; open Monoid M₂ in
                          ∀ {x} -> f·₁ x ≈ f·₂ x
                      }
  ; isIEquivalence = record
      { refl  = λ{ {M₁ , M₂}     -> Monoid.refl  M₂     }
      ; sym   = λ{ {M₁ , M₂} p   -> Monoid.sym   M₂ p   }
      ; trans = λ{ {M₁ , M₂} p q -> Monoid.trans M₂ p q }
      }
  }

Mon : ∀ {α} -> Set α -> (β : Level) -> Category (α ⊔ suc β) (α ⊔ β) (α ⊔ β)
Mon A β = record
  { Obj      = Monoid A β
  ; _⇒_      = Homo
  ; setoid   = Homo-ISetoid₂
  ; id       = idʰ
  ; _∘_      = _∘ʰ_
  ; idˡ      = λ {M₁ M₂}       -> Monoid.refl M₂
  ; idʳ      = λ {M₁ M₂}       -> Monoid.refl M₂
  ; assoc    = λ {M₁ M₂ M₃ M₄} -> Monoid.refl M₄
  ; ∘-resp-≈ = λ {M₁ M₂ M₃ H₁ H₂ H₃ H₄} q p -> Monoid.trans M₃ q (Homo.f-resp-≈ H₂ p)
  }

Monoid-Category : ∀ {α β} {A : Set α} -> Monoid A β -> Category zero α β
Monoid-Category {A = A} M = record
  { Obj      = ⊤
  ; _⇒_      = λ _ _ -> A
  ; setoid   = let open Indexed setoid in isetoid
  ; id       = ε
  ; _∘_      = _∙_
  ; idˡ      = idˡ
  ; idʳ      = idʳ
  ; assoc    = assoc
  ; ∘-resp-≈ = ∙-resp-≈
  } where open Monoid M

Homo-Functor : ∀ {α₁ α₂ β₁ β₂} {A₁ : Set α₁} {A₂ : Set α₂}
                 {M₁ : Monoid A₁ β₁} {M₂ : Monoid A₂ β₂}
             -> Homo M₁ M₂ -> Functor (Monoid-Category M₁) (Monoid-Category M₂)
Homo-Functor H = record
  { F⇒       = f·
  ; F-id     = f-ε
  ; F-∘      = f-∙
  ; F-resp-≈ = f-resp-≈
  } where open Homo H
