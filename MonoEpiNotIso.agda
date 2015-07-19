-- Taken from "Category Theory", Steve Awodey.
-- I'm using categories instead of posets.
-- Looks like I messed up something.

module Categories.MonoEpiNotIso where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (setoid)
open import Data.Empty

open import Categories.Category
open import Categories.Functor
open import Categories.Morphism

infix 9 _∘₁_ _∘₂_

data D : Set where
  x y z : D
      
data _≤₁_ : D -> D -> Set where
  refl₁ : ∀ {x} -> x ≤₁ x
  x≤₁y  :          x ≤₁ y
  x≤₁z  :          x ≤₁ z
  y≤₁z  :          y ≤₁ z
      
data _≤₂_ : D -> D -> Set where
  refl₂ : ∀ {x} -> x ≤₂ x
  x≤₂y  :          x ≤₂ y
  x≤₂z  :          x ≤₂ z

_∘₁_ : ∀ {a b c} -> b ≤₁ c -> a ≤₁ b -> a ≤₁ c
refl₁ ∘₁ a≤b   = a≤b
x≤₁y  ∘₁ refl₁ = x≤₁y
x≤₁z  ∘₁ refl₁ = x≤₁z
y≤₁z  ∘₁ refl₁ = y≤₁z
y≤₁z  ∘₁ x≤₁y  = x≤₁z

idˡ₁ : ∀ {a b : D} {a≤b : a ≤₁ b} -> refl₁ ∘₁ a≤b ≡ a≤b
idˡ₁ = refl

idʳ₁ : ∀ {a b : D} {a≤b : a ≤₁ b} -> a≤b ∘₁ refl₁ ≡ a≤b
idʳ₁ {a≤b = refl₁} = refl
idʳ₁ {a≤b = x≤₁y } = refl
idʳ₁ {a≤b = x≤₁z } = refl
idʳ₁ {a≤b = y≤₁z } = refl

assoc₁ : ∀ {a b c d : D} (c≤d : c ≤₁ d) {b≤c : b ≤₁ c} {a≤b : a ≤₁ b}
       -> (c≤d ∘₁ b≤c) ∘₁ a≤b ≡ c≤d ∘₁ (b≤c ∘₁ a≤b)
assoc₁ refl₁                 = refl
assoc₁ x≤₁y  {refl₁}         = refl
assoc₁ x≤₁z  {refl₁}         = refl
assoc₁ y≤₁z  {refl₁}         = refl
assoc₁ y≤₁z  {x≤₁y } {refl₁} = refl

∘₁-resp-≡ : ∀ {a b c} {b≤c₁ b≤c₂ : b ≤₁ c} {a≤b₁ a≤b₂ : a ≤₁ b}
          -> b≤c₁ ≡ b≤c₂ -> a≤b₁ ≡ a≤b₂ -> b≤c₁ ∘₁ a≤b₁ ≡ b≤c₂ ∘₁ a≤b₂
∘₁-resp-≡ refl refl = refl

_∘₂_ : ∀ {a b c} -> b ≤₂ c -> a ≤₂ b -> a ≤₂ c
refl₂ ∘₂ a≤b   = a≤b
x≤₂y  ∘₂ refl₂ = x≤₂y
x≤₂z  ∘₂ refl₂ = x≤₂z

idˡ₂ : ∀ {a b : D} {a≤b : a ≤₂ b} -> refl₂ ∘₂ a≤b ≡ a≤b
idˡ₂ = refl

idʳ₂ : ∀ {a b : D} {a≤b : a ≤₂ b} -> a≤b ∘₂ refl₂ ≡ a≤b
idʳ₂ {a≤b = refl₂} = refl
idʳ₂ {a≤b = x≤₂y } = refl
idʳ₂ {a≤b = x≤₂z } = refl

assoc₂ : ∀ {a b c d : D} (c≤d : c ≤₂ d) {b≤c : b ≤₂ c} {a≤b : a ≤₂ b}
       -> (c≤d ∘₂ b≤c) ∘₂ a≤b ≡ c≤d ∘₂ (b≤c ∘₂ a≤b)
assoc₂ refl₂         = refl
assoc₂ x≤₂y  {refl₂} = refl
assoc₂ x≤₂z  {refl₂} = refl

∘₂-resp-≡ : ∀ {a b c} {b≤c₁ b≤c₂ : b ≤₂ c} {a≤b₁ a≤b₂ : a ≤₂ b}
          -> b≤c₁ ≡ b≤c₂ -> a≤b₁ ≡ a≤b₂ -> b≤c₁ ∘₂ a≤b₁ ≡ b≤c₂ ∘₂ a≤b₂
∘₂-resp-≡ refl refl = refl

C₁ : Category zero zero zero
C₁ = record
  { Obj      = D
  ; _⇒_      = _≤₁_
  ; setoid   = ≡-IndexedSetoid
  ; id       = refl₁
  ; _∘_      = _∘₁_
  ; idˡ      = idˡ₁
  ; idʳ      = idʳ₁
  ; assoc    = assoc₁
  ; ∘-resp-≈ = ∘₁-resp-≡
  }

C₂ : Category zero zero zero
C₂ = record
  { Obj      = D
  ; _⇒_      = _≤₂_
  ; setoid   = ≡-IndexedSetoid
  ; id       = refl₂
  ; _∘_      = _∘₂_
  ; idˡ      = idˡ₂
  ; idʳ      = idʳ₂
  ; assoc    = assoc₂
  ; ∘-resp-≈ = ∘₂-resp-≡
  }

bij : ∀ {a b} -> a ≤₂ b -> a ≤₁ b
bij refl₂ = refl₁
bij x≤₂y  = x≤₁y
bij x≤₂z  = x≤₁z

bij-∘ : ∀ {a b c} -> (b≤c : b ≤₂ c) -> (a≤b : a ≤₂ b) -> bij (b≤c ∘₂ a≤b) ≡ bij b≤c ∘₁ bij a≤b
bij-∘ refl₂ a≤b   = refl
bij-∘ x≤₂y  refl₂ = refl
bij-∘ x≤₂z  refl₂ = refl

fun : Functor C₂ C₁
fun = record
  { F·       = id→
  ; F⇒       = bij
  ; F-id     = refl
  ; F-∘      = bij-∘
  ; F-resp-≈ = cong bij
  }

module _ where
  open HeteroIndexedEquality

  bij-inj : ∀ {a b c d} {a≤b : a ≤₂ b} {c≤d : c ≤₂ d}
          -> bij a≤b [ uncurry _≤₁_ ]≅ bij c≤d
          ->     a≤b [ uncurry _≤₂_ ]≅     c≤d
  bij-inj {a≤b = refl₂} {c≤d = refl₂} (hetero _) = hrefl
  bij-inj {a≤b = x≤₂y } {c≤d = x≤₂y } (hetero _) = hrefl
  bij-inj {a≤b = x≤₂z } {c≤d = x≤₂z } (hetero _) = hrefl

-- The simplest definition of `bij-epi' I've found. Not very satisfactory.
-- I didn't expect, that Agda can instantiate `a≤b' in each `p'.
-- Moreover, Agda rejects `p' in the last case, which is impressive.
-- Is this related to inferring arguments of constructor-headed functions? 
bij-epi : ∀ {α β γ} {Obj : Set α} {g₀ h₀ : D -> Obj} {_⇒_ : Obj -> Obj -> Set β}
        -> (setoid : IndexedSetoid (uncurry _⇒_) γ)
        -> (g : ∀ {a b} -> a ≤₁ b -> g₀ a ⇒ g₀ b)
        -> (h : ∀ {a b} -> a ≤₁ b -> h₀ a ⇒ h₀ b)
        -> let open Hetero setoid in
           (∀ {a b} {a≤b : a ≤₂ b} -> g (bij a≤b) ≋ h (bij a≤b))
        -> (∀ {a b} {a≤b : a ≤₁ b} -> g  a≤b      ≋ h  a≤b     )
bij-epi setoid g h p {a≤b = refl₁} = p
bij-epi setoid g h p {a≤b = x≤₁y } = p
bij-epi setoid g h p {a≤b = x≤₁z } = p
bij-epi setoid g h p {a≤b = y≤₁z } = {!!} -- Nope, that's not the case.

fun-Mono : Mono Cat fun
fun-Mono = record { mono = λ p -> bij-inj p }

fun-Epi  : Epi  Cat fun
fun-Epi  = record { epi  = λ {C G H} -> bij-epi (setoid C) (F⇒ G) (F⇒ H) }
  where open Functor; open Category

postulate
  ¬-fun-Iso : ¬ (Iso Cat fun)

¬Mono&Epi->Iso : (∀ {α β γ} {C : Category α β γ} -> let open Category C in
                    ∀ {A B : Obj} {f : A ⇒ B}-> Mono C f -> Epi C f -> Iso C f
                 ) -> ⊥
¬Mono&Epi->Iso c = ¬-fun-Iso (c fun-Mono fun-Epi)
