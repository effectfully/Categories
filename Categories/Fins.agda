module Categories.Categories.Fins where

open import Data.Nat.Base
open import Data.Fin
open import Data.Vec
open import Data.Vec.Properties

open import Categories.Examples.Eqclasses.Utilities
open import Categories.Category renaming (zero to lzero)

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
