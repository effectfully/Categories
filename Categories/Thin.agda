module Categories.Categories.Thin where

open import Relation.Binary hiding (_⇒_)
open import Data.Unit.Base hiding (_≤_)
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.LCM
open import Data.Fin as F hiding (_≤_)

open import Categories.Category renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
import Categories.Universal.Limit.Product     as Product
import Categories.Universal.Colimit.Coproduct as Coproduct

record ThinCategory α β : Set (lsuc (α ⊔ₗ β)) where
  infix  3 _⇒_
  infixr 9 _∘_
  
  field
    Obj : Set α
    _⇒_ : Obj -> Obj -> Set β
    id  : ∀ {A}     -> A ⇒ A
    _∘_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C

thin : ∀ {α β} -> ThinCategory α β -> Category α β _
thin C = record
  { Obj    = Obj
  ; _⇒_    = _⇒_
  ; setoid = ⊤-ISetoid
  ; id     = id
  ; _∘_    = _∘_
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

  open Product Le; open Coproduct Le

  Le-binaryProducts : BinaryProducts
  Le-binaryProducts {n} {m} = record
    { Ob  = n ⊓ m
    ; π¹  = m⊓n≤m n m
    ; π²  = m⊓n≤n n m
    ; _↑_ = p≤m⊓n
    } where
        m⊓n≤n : ∀ m n -> m ⊓ n ≤ n
        m⊓n≤n  0       n      = z≤n
        m⊓n≤n (suc m)  0      = z≤n
        m⊓n≤n (suc m) (suc n) = s≤s (m⊓n≤n m n)

        p≤m⊓n : ∀ {m n p} -> p ≤ m -> p ≤ n -> p ≤ m ⊓ n
        p≤m⊓n  z≤n       p≤n      = z≤n
        p≤m⊓n (s≤s p≤m) (s≤s p≤n) = s≤s (p≤m⊓n p≤m p≤n)

  Le-binaryCoproducts : BinaryCoproducts
  Le-binaryCoproducts {n} {m} = record
    { Ob  = n ⊔ m
    ; ι¹  = m≤m⊔n n m
    ; ι²  = n≤m⊔n n m
    ; _↓_ = m⊔n≤p
    } where
        n≤m⊔n : ∀ m n -> n ≤ m ⊔ n
        n≤m⊔n  0       n      = refl
        n≤m⊔n (suc m)  0      = z≤n
        n≤m⊔n (suc m) (suc n) = s≤s (n≤m⊔n m n)

        m⊔n≤p : ∀ {m n p} -> m ≤ p -> n ≤ p -> m ⊔ n ≤ p
        m⊔n≤p  z≤n       n≤p      = n≤p
        m⊔n≤p (s≤s m≤p)  z≤n      = s≤s m≤p
        m⊔n≤p (s≤s m≤p) (s≤s n≤p) = s≤s (m⊔n≤p m≤p n≤p)

module _ where
  open Poset poset
  
  Div : Category _ _ _
  Div = thin record
    { Obj = ℕ
    ; _⇒_ = _∣_
    ; id  = reflexive prefl
    ; _∘_ = flip trans
    } 

  open Product Div; open Coproduct Div

  Div-binaryProducts : BinaryProducts
  Div-binaryProducts {n} {m} = record
    { Ob  = d
    ; π¹  = π¹
    ; π²  = π²
    ; _↑_ = _↑_
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

  Div-binaryCoproducts : BinaryCoproducts
  Div-binaryCoproducts {n} {m} = record
    { Ob  = d
    ; ι¹  = ι¹
    ; ι²  = ι²
    ; _↓_ = _↓_
    } where
        p : ∃ (LCM n m)
        p = lcm n m

        d = proj₁ p

        open LCM.LCM (proj₂ p)

        ι¹ : n ∣ d
        ι¹ = proj₁ commonMultiple

        ι² : m ∣ d
        ι² = proj₂ commonMultiple

        _↓_ : ∀ {p} -> n ∣ p -> m ∣ p -> d ∣ p
        _↓_ = curry least
