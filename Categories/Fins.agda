module Categories.Categories.Fins where

open import Data.Nat.Base
open import Data.Fin
open import Data.Vec as Vec
open import Data.Vec.Properties

open import Categories.Category hiding (suc) renaming (zero to lzero)

infixl 7 _!_ _‼_

_↤_ : ℕ -> ℕ -> Set
n ↤ m = Vec (Fin m) n

_!_ : ∀ {α n} {A : Set α} -> Vec A n -> Fin n -> A
_!_ = flip lookup

_‼_ : ∀ {α n m} {A : Set α} -> Vec A n -> m ↤ n -> Vec A m
xs ‼ is = Vec.map (xs !_) is

Fins : Category lzero lzero lzero
Fins = record
  { Obj      = ℕ
  ; _⇒_      = _↤_
  ; setoid   = ≡-ISetoid
  ; id       = allFin _
  ; _∘_      = _‼_
  ; idˡ      = ptrans (map-cong lookup-allFin _) (map-id _)
  ; idʳ      = map-lookup-allFin _
  ; assoc    = assoc
  ; ∘-resp-≈ = cong₂ _‼_
  } where
      assoc : ∀ {n m p q} {h : p ↤ q} {g : m ↤ p} {f : n ↤ m} -> (h ‼ g) ‼ f ≡ h ‼ (g ‼ f) 
      assoc {f = []   } = prefl
      assoc {f = i ∷ _} = cong₂ _∷_ (‼-! i) assoc where
        ‼-! : ∀ {n m p} {g : m ↤ p} {f : n ↤ m} -> ∀ i -> (g ‼ f) ! i ≡ g ! (f ! i)
        ‼-! {f = []   }  ()
        ‼-! {f = _ ∷ _}  zero   = prefl
        ‼-! {f = _ ∷ _} (suc i) = ‼-! i

open import Categories.Object Fins

initial : Initial
initial = record
  { Ob        = 0
  ; ↜         = []
  ; universal = λ{ {_} {[]} -> prefl }
  }

binaryCoproducts : BinaryCoproducts
binaryCoproducts {n} {m} = {!!}
