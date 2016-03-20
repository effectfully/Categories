module Categories.STLC.CCC where

open import Categories.Category
open import Categories.Category.CCC
open import Categories.STLC.OPE
open import Categories.STLC.Term

-- Just an approximation. The actual equality must be βη (convertibility? normalization?).
-- And we probably need explicit substitutions to make proofs tractable.

Term : Category _ _ _
Term = record
  { Obj      = Type
  ; _⇒_      = _⊢₁_
  ; setoid   = ≡-ISetoid
  ; id       = var vz
  ; _∘_      = _[_]₁
  ; idˡ      = prefl
  ; idʳ      = sub-id* _
  ; assoc    = λ {_ _ _ _ x y z} -> sub-sub (ø ▷ z) (ø ▷ y) x
  ; ∘-resp-≈ = cong₂ _[_]₁ 
  }

open import Categories.Object Term

termCCC : CCC Term
termCCC = record
  { terminal       = record
      { Ob     = ⋆
      ; ↝      = unit
      ; ↝-univ = {!!}
      }
  ; binaryProducts = λ σ τ -> record
      { Ob      = σ & τ
      ; π¹      = fst (var vz)
      ; π²      = snd (var vz)
      ; ⟨_,_⟩   = pair
      ; ⟨⟩-inj  = {!!}
      ; ⟨⟩-univ = {!!}
      }
  ; exponentials   = λ τ σ -> record
      { B^A       = σ ⇒ τ
      ; eval      = fst (var vz) · snd (var vz)
      ; curr      = λ b -> ƛ (b [ pair (var (vs vz)) (var vz) ]₁)
      ; curr-inj  = {!!}
      ; curr-univ = {!!}
      }
  }
