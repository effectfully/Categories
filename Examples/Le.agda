module Categories.Examples.Le where

open import Relation.Binary
open import Data.Nat
open import Data.Nat.Properties

open DecTotalOrder decTotalOrder hiding (_≤_)

open import Categories.Category hiding (_⊔_)

Le : Category _ _ _
Le = record
  { Obj    = ℕ
  ; _⇒_    = _≤_
  ; setoid = ⊤-ISetoid
  ; id     = refl
  ; _∘_    = flip trans
  }

open import Categories.Object.Limit.Product     Le
open import Categories.Object.Colimit.Initial   Le
open import Categories.Object.Colimit.Coproduct Le

initial : Initial
initial = record { ↜ = z≤n }

binaryProducts : BinaryProducts
binaryProducts {n} {m} = record
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

binaryCoproducts : BinaryCoproducts
binaryCoproducts {n} {m} = record
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
