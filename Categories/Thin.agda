module Categories.Categories.Thin where

open import Level
open import Relation.Binary hiding (_⇒_)
open import Data.Unit.Base hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Fin as F hiding (_≤_)

open import Categories.Category
import Categories.Universal.Limit.Product as Product

record ThinCategory α β : Set (Level.suc (α Level.⊔ β)) where
  infix  3 _⇒_
  infixr 9 _∘_
  
  field
    Obj : Set α
    _⇒_ : Obj -> Obj -> Set β
    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

thin : ∀ {α β} -> ThinCategory α β -> Category α β _
thin C = record
  { Obj      = Obj
  ; _⇒_      = _⇒_
  ; setoid   = ⊤-ISetoid
  ; id       = id
  ; _∘_      = _∘_
  ; idˡ      = _
  ; idʳ      = _
  ; assoc    = _
  ; ∘-resp-≈ = _
  } where open ThinCategory C

Discrete : ∀ {α} -> Set α -> Category α α _
Discrete A = thin record
  { Obj = A
  ; _⇒_ = _≡_
  ; id  = prefl
  ; _∘_ = flip ptrans
  }

One = Discrete ⊤

module _ where
  open DecTotalOrder decTotalOrder hiding (_≤_)
  
  Nat : ℕ -> Category _ _ _
  Nat n = thin record
    { Obj = Fin n
    ; _⇒_ = F._≤_
    ; id  = refl
    ; _∘_ = flip trans
    }

  Le : Category _ _ _
  Le = thin record
    { Obj = ℕ
    ; _⇒_ = _≤_
    ; id  = refl
    ; _∘_ = flip trans
    }

  open Product Le

  Le-binaryProducts : BinaryProducts
  Le-binaryProducts {n} {m} = record
    { Ob        = n ⊓ m
    ; π¹        = m⊓n≤m n m
    ; π²        = m⊓n≤n n m
    ; _↑_       = p≤m⊓n
    ; ↑-inj     = _
    ; universal = _
    } where
        m⊓n≤n : ∀ m n -> m ⊓ n ≤ n
        m⊓n≤n  0       n      = z≤n
        m⊓n≤n (suc m)  0      = z≤n
        m⊓n≤n (suc m) (suc n) = s≤s (m⊓n≤n m n)

        p≤m⊓n : ∀ {m n p} -> p ≤ m -> p ≤ n -> p ≤ m ⊓ n
        p≤m⊓n  z≤n       p≤n      = z≤n
        p≤m⊓n (s≤s p≤m) (s≤s p≤n) = s≤s (p≤m⊓n p≤m p≤n)

module _ where
  open Poset poset
  
  Mul : Category _ _ _
  Mul = thin record
    { Obj = ℕ
    ; _⇒_ = _∣_
    ; id  = reflexive prefl
    ; _∘_ = flip trans
    } 

  open Product Mul

  Mul-binaryProducts : BinaryProducts
  Mul-binaryProducts {n} {m} = record
    { Ob        = d
    ; π¹        = π¹
    ; π²        = π²
    ; _↑_       = _↑_
    ; ↑-inj     = _
    ; universal = _
    } where
        p : ∃ (GCD n m)
        p = gcd n m

        d = proj₁ p

        open GCD.GCD (proj₂ p)

        π¹ : d ∣ n
        π¹ = proj₁ commonDivisor

        π² : d ∣ m
        π² = proj₂ commonDivisor

        _↑_ : ∀ {p} -> p ∣ n -> p ∣ m -> p ∣ d
        _↑_ = curry greatest
