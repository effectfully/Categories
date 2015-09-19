module Categories.Categories.Fins where

open import Data.Nat.Base
open import Data.Fin

open import Categories.Category
open import Categories.Object.Colimit.Coequalizer
open import Categories.Utilities.Coequalize.Coequalize

open ≡-Reasoning

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

coequalizers : Coequalizers Fins
coequalizers {n} {m} {f} {g} =
  let c = coeq f g
      π = restrict c
      (s , p) = invert-restrict c
  in record
    { π       = π
    ; [_]∣_∣  = λ u q -> u ∘′ s
    ; π-comm  = restrict-preserves-≡ c ∘′ coeq-comm f g
    ; []-inj  = λ {_ h₁ h₂ q₁ q₂} r i ->
        begin
          h₁  i            ←⟨ coeq-univ h₁ q₁ i                         ⟩
          h₁ (c i)         ←⟨ cong h₁ (restrict-reflects-≡ c (p (π i))) ⟩
          h₁ (c (s (π i))) →⟨ coeq-univ h₁ q₁ (s (π i))                 ⟩
          h₁ (s (π i))     →⟨ r (π i)                                   ⟩
          h₂ (s (π i))     ←⟨ coeq-univ h₂ q₂ (s (π i))                 ⟩
          h₂ (c (s (π i))) →⟨ cong h₂ (restrict-reflects-≡ c (p (π i))) ⟩
          h₂ (c i)         →⟨ coeq-univ h₂ q₂ i                         ⟩
          h₂  i
        ∎
    ; []-univ = λ {_ _ u} q i -> ptrans (psym (q (s i))) (cong u (p i))
    }
