module Categories.STLC.Structures.OPE where

open import Categories.Category
open import Categories.STLC.Core
open import Categories.STLC.Properties

OPE : ∀{α} -> Set α -> Category α α α
OPE A = record
  { Obj      = Listʳ A
  ; _⇒_      = _⊆_
  ; setoid   = ≡-ISetoid
  ; id       = idˢ
  ; _∘_      = _∘ˢ_
  ; idˡ      = idˡˢ
  ; idʳ      = idʳˢ
  ; assoc    = λ {_ _ _ _ ι₃ ι₂ ι₁} -> assocˢ ι₃ ι₂ ι₁
  ; ∘-resp-≈ = cong₂ _∘ˢ_
  }
