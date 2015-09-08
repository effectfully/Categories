module Categories.STLC.Ext where

open import Relation.Binary.PropositionalEquality

infixr 0 ext_ extᵢ_

postulate
  ext_  : ∀ {α β} {A : Set α} {B : A -> Set β} {f g : ∀ x -> B x}
        -> (∀ x -> f x ≡ g x) -> f ≡ g
  extᵢ_ : ∀ {α β} {A : Set α} {B : A -> Set β} {f g : ∀ {x} -> B x}
        -> (∀ {x} -> f {x} ≡ g {x}) -> (λ {x} -> f {x}) ≡ (λ {x} -> g {x})
