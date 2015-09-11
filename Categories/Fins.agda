module Categories.Categories.Fins where

open import Data.Nat.Base
open import Data.Fin

open import Categories.Category
open import Categories.Object.Colimit.Coequalizer
open import Categories.Utilities.Coequalize.Coequalize

Fins : Category _ _ _
Fins = record
  { Obj      = ℕ
  ; _⇒_      = _↦_
  ; setoid   = coerceⁱˢ →-ISetoid₂
  ; id       = id′
  ; _∘_      = λ g f -> g ∘′ f
  ; idˡ      = λ i -> prefl
  ; idʳ      = λ i -> prefl
  ; assoc    = λ i -> prefl
  ; ∘-resp-≈ = ∘′-resp-≡
  }

-- restrict-injective
coequalizers : Coequalizers Fins
coequalizers {n} {m} {f} {g} = let (s , p) = invert-restrict c in record
  { π         = π
  ; [_]∣_∣    = λ u q -> u ∘′ s
  ; comm      = restrict-preserves-≡ c ∘′ coeq-comm f g
  ; []-inj    = λ {_ f' g'} r i -> subst (λ i' -> f' i' ≡ g' i') {!p (π i)!} (r (π i))
  ; universal = λ {_ _ u} q i -> ptrans (psym (q (s i))) (cong u (p i))
  } where c = coeq f g; π = restrict c
