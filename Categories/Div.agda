module Categories.Categories.Div where

open import Relation.Binary
open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.LCM

open Poset poset

open import Categories.Category
  
Div : Category _ _ _
Div = record
  { Obj    = ℕ
  ; _⇒_    = _∣_
  ; setoid = ⊤-ISetoid
  ; id     = reflexive prefl
  ; _∘_    = flip trans
  } 

open import Categories.Object Div

initial : Initial
initial = record { ↜ = 1∣ _ }

binaryProducts : BinaryProducts
binaryProducts {n} {m} = record
  { Ob    = d
  ; π¹    = π¹
  ; π²    = π²
  ; ⟨_,_⟩ = ⟨_,_⟩
  } where
      p : ∃ (GCD n m)
      p = gcd n m

      d = proj₁ p

      open GCD.GCD (proj₂ p)

      π¹ : d ∣ n
      π¹ = proj₁ commonDivisor

      π² : d ∣ m
      π² = proj₂ commonDivisor

      ⟨_,_⟩ : ∀ {p} -> p ∣ n -> p ∣ m -> p ∣ d
      ⟨_,_⟩ = curry greatest

binaryCoproducts : BinaryCoproducts
binaryCoproducts {n} {m} = record
  { Ob    = d
  ; ι¹    = ι¹
  ; ι²    = ι²
  ; [_,_] = [_,_]
  } where
      p : ∃ (LCM n m)
      p = lcm n m

      d = proj₁ p

      open LCM.LCM (proj₂ p)

      ι¹ : n ∣ d
      ι¹ = proj₁ commonMultiple

      ι² : m ∣ d
      ι² = proj₂ commonMultiple

      [_,_] : ∀ {p} -> n ∣ p -> m ∣ p -> d ∣ p
      [_,_] = curry least
