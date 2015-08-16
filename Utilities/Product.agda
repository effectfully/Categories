module Categories.Utilities.Product where

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product

,′-inj : ∀ {α β} {A : Set α} {B : Set β} {x x' : A} {y y' : B}
       -> (x , y) ≡ (x' , y') -> x ≡ x' × y ≡ y'
,′-inj refl = refl , refl

-- -- More generic, but less useable.
-- _-<_>-_ : ∀ {α β γ δ ε ζ η} {A : Set α} {B : A -> Set β} {C : ∀ {a} -> B a -> Set γ}
--             {D : ∀ {a} {b : B a} -> C b -> Set δ} {E : ∀ {a} {b : B a} -> C b -> Set ε}
--             {F : ∀ {a a'} {b : B a} {b' : B a'} {c : C b} {c' : C b'} -> D c -> E c' -> Set ζ}
--             {G : ∀ {a a'} {b : B a} {b' : B a'} {c : C b} {c' : C b'} {d : D c} {e : E c'}
--                  -> F d e -> Set η}
--         -> (f : ∀ a -> {b : B a} -> (c : C b) -> E c)
--         -> (∀ {a a'} {b : B a} {b' : B a'} {c : C b} {c' : C b'} {d' : D c'}
--             -> (e : E c) -> (f : F d' e) -> G f)
--         -> (g : ∀ {a} -> (b : B a) -> {c : C b} -> (d : D c) -> F d (f a c))
--         -> (p : Σ A B)
--         -> (q : Σ (C _) D)
--         -> G (g _ _)
-- (f -< h >- g) (a , b) (c , d) = h (f a c) (g b d)

-- _-<_>-_ : ∀ {α β γ δ ε ζ η} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
--             {D : ∀ {a a'} -> B a -> C a' -> Set δ} {E : ∀ {a} -> C a -> Set ε}
--             {F : ∀ {a a' a''} {b : B a} {c : C a'} {c' : C a''} -> D b c -> E c' -> Set ζ}
--             {G : ∀ {a a' a''} {b : B a} {c : C a'} {c' : C a''} {d : D b c} {e : E c'}
--                  -> F d e -> Set η}
--         -> (f : ∀ a -> (c : C a) -> E c)
--         -> (∀ {a a' a''} {b : B a} {c : C a'} {c' : C a''} {d : D b c}
--             -> (e : E c') -> (f : F d e) -> G f)
--         -> (g : ∀ {a a'} {c : C a} -> (b : B a') -> (d : D b c) -> F d (f a c))
--         -> (p : Σ A B)
--         -> (q : Σ (C _) (D _))
--         -> G (g _ _)
-- (f -< h >- g) (a , b) (c , d) = h (f a c) (g b d)

_<×>_ : ∀ {α β γ δ ε ζ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
          {D : ∀ {a a'} -> B a -> C a' -> Set δ}
      -> (∀ a -> C a -> Set ε)
      -> (∀ {a a'} {c : C a} -> (b : B a') -> (d : D b c) -> Set ζ)
      -> (p : Σ A B)
      -> (q : Σ (C _) (D _))
      -> Set (ε ⊔ ζ)
(F <×> G) (a , b) (c , d) = F a c × G b d

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
