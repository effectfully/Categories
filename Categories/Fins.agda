module Categories.Categories.Fins where

open import Data.Nat.Base
open import Data.Fin
open import Data.Vec
open import Data.Vec.Properties

open import Categories.Category renaming (zero to lzero) hiding (map)

Fins : Category lzero lzero lzero
Fins = record
  { Obj      = ℕ
  ; _⇒_      = λ n m -> Vec (Fin m) n
  ; setoid   = ≡-ISetoid
  ; id       = allFin _
  ; _∘_      = _∘_
  ; idˡ      = ptrans (map-cong lookup-allFin _) (map-id _)
  ; idʳ      = map-lookup-allFin _
  ; assoc    = assoc
  ; ∘-resp-≈ = cong₂ _∘_
  } where
      infixr 9 _∘_

      _∘_ : ∀ {n m p} -> Vec (Fin p) m -> Vec (Fin m) n -> Vec (Fin p) n
      g ∘ f = map (flip lookup g) f

      assoc : ∀ {n m p q} {h : Vec (Fin q) p} {g : Vec (Fin p) m} {f : Vec (Fin m) n}
            -> (h ∘ g) ∘ f ≡ h ∘ (g ∘ f) 
      assoc {f = []   } = prefl
      assoc {f = i ∷ _} = cong₂ _∷_ (lookup-∘ i) assoc where
        lookup-∘ : ∀ {n m p} {g : Vec (Fin p) m} {f : Vec (Fin m) n}
                 -> ∀ i -> lookup i (g ∘ f) ≡ lookup (lookup i f) g
        lookup-∘ {f = []   }  ()
        lookup-∘ {f = _ ∷ _}  zero   = prefl
        lookup-∘ {f = _ ∷ _} (suc i) = lookup-∘ i
