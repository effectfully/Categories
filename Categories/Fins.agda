module Categories.Categories.Fins where

open import Data.Nat.Base
open import Data.Fin hiding (_+_)

open import Categories.Category renaming (zero to lzero; suc to lsuc)
open import Categories.Utilities.Coequalize.Coequalize

open ≡-Reasoning

Fins : Category lzero lzero lzero
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

open import Categories.Object Fins

binaryCoproducts : BinaryCoproducts
binaryCoproducts {n} {m} = record
  { Ob      = n + m
  ; ι¹      = inject+ m
  ; ι²      = raise n
  ; [_,_]   = [_,_]
  ; []-inj  = []-inj
  ; []-univ = []-univ
  } where
      [_,_] : ∀ {n m α} {A : Set α} -> (Fin n -> A) -> (Fin m -> A) -> Fin (n + m) -> A
      [_,_] {0}     f g  i      = g i
      [_,_] {suc n} f g  zero   = f zero
      [_,_] {suc n} f g (suc i) = [ f ∘′ suc , g ] i

      []-inj : ∀ {n m α} {A : Set α} {f₁ f₂ : Fin n -> A} {g₁ g₂ : Fin m -> A}
             -> [ f₁ , g₁ ] ≗ₚ [ f₂ , g₂ ] -> f₁ ≗ₚ f₂ ×ₚ g₁ ≗ₚ g₂
      []-inj {0}     p = (λ()) , p
      []-inj {suc n} p = map (caseFin (p zero)) id′ ([]-inj (p ∘′ suc))
 
      []-univ : ∀ {n m α} {A : Set α} {f : Fin n -> A} {g : Fin m -> A} {u : Fin (n + m) -> A}
              -> u ∘′ inject+ m ≗ₚ f -> u ∘′ raise n ≗ₚ g -> [ f , g ] ≗ₚ u
      []-univ {0}     p q  i      = psym (q i)
      []-univ {suc n} p q  zero   = psym (p zero)
      []-univ {suc n} p q (suc i) = []-univ (p ∘′ suc) q i

coequalizers : Coequalizers
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
          h₁  i            ←⟨ coeq-univ h₁ q₁  i                        ⟩
          h₁ (c  i)        ←⟨ cong h₁ (restrict-reflects-≡ c (p (π i))) ⟩
          h₁ (c (s (π i))) →⟨ coeq-univ h₁ q₁ (s (π i))                 ⟩
          h₁ (s (π i))     →⟨ r (π i)                                   ⟩
          h₂ (s (π i))     ←⟨ coeq-univ h₂ q₂ (s (π i))                 ⟩
          h₂ (c (s (π i))) →⟨ cong h₂ (restrict-reflects-≡ c (p (π i))) ⟩
          h₂ (c  i)        →⟨ coeq-univ h₂ q₂  i                        ⟩
          h₂  i
        ∎
    ; []-univ = λ {_ _ u} q i -> ptrans (psym (q (s i))) (cong u (p i))
    }

pushouts : Pushouts
pushouts = Coproduct&Coequalizer->Pushout binaryCoproducts coequalizers
