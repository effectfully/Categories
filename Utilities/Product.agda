module Categories.Utilities.Product where

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product

,′-inj : ∀ {α β} {A : Set α} {B : Set β} {x x' : A} {y y' : B}
       -> (x , y) ≡ (x' , y') -> x ≡ x' × y ≡ y'
,′-inj refl = refl , refl

_-<_>-_ : ∀ {α β γ δ ε ζ η} {A : Set α} {B : A -> Set β} {C : Set γ} {D : C -> Set δ}
            {E : A -> C -> Set ε} {F : ∀ {a a' c c'} -> E a' c' -> B a -> D c -> Set ζ}
            {G : ∀ {a a' c c'} {b : B a'} {d : D c'} -> (e : E a c) -> F e b d -> Set η}
        -> (f : ∀ a c -> E a c)
        -> (∀ {a a' c c'} {b : B a'} {d : D c'} -> (e : E a c) -> (f : F e b d) -> G e f)
        -> (g : ∀ {a c} -> (b : B a) -> (d : D c) -> F (f a c) b d)
        -> (p : Σ A B)
        -> (q : Σ C D)
        -> G (f (proj₁ p) (proj₁ q)) (g (proj₂ p) (proj₂ q))
(f -< h >- g) (a , b) (c , d) = h (f a c) (g b d)

record ∃ᵢ {α β} {A : Set α} (B : A -> Set β) : Set (α ⊔ β) where
  constructor _,ᵢ_
  field
    iproj₁  : A
    .iproj₂ : B iproj₁
open ∃ᵢ public

,ᵢ-inj₁ : ∀ {α β} {A : Set α} {B : A -> Set β} {x x' : A} .{y : B x} .{y' : B x'}
        -> (x ,ᵢ y) ≡ (x' ,ᵢ y') -> x ≡ x'
,ᵢ-inj₁ refl = refl

-- This looks like a half of the η-rule, but it has the same power and is more convenient actually.
∃ᵢ-η : ∀ {α β} {A : Set α} {B : A -> Set β} {x : A} {p : ∃ᵢ B}
     -> (r : iproj₁ p ≡ x) -> (x ,ᵢ subst B r (iproj₂ p)) ≡ p
∃ᵢ-η refl = refl
