module Categories.Utilities.Coequalize.Coequalize where

open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Fin
open import Data.Fin.Properties
open import Data.Maybe.Base as M
open import Data.Sum        as S
open import Data.Product    as P

_↦_ : ℕ -> ℕ -> Set
n ↦ m = Fin n -> Fin m

caseFin : ∀ {α n} {A : Fin (suc n) -> Set α}
        -> A zero -> (∀ i -> A (suc i)) -> (i : Fin (suc n)) -> A i
caseFin z f  zero   = z
caseFin z f (suc i) = f i

min-max : ∀ {n} -> Fin n -> Fin n -> Fin n × Fin n
min-max  zero    j      = zero , j
min-max (suc i)  zero   = zero , suc i
min-max (suc i) (suc j) = P.map suc suc (min-max i j)

[_/_] : ∀ {n} -> Fin n -> Fin n -> Fin n -> Fin n
[ k / j ] i = if ⌊ i ≟ j ⌋ then k else i

subst-same : ∀ {n} (k j : Fin n) -> [ k / j ] j ≡ k
subst-same k j with j ≟ j
... | yes _ = refl
... | no  c = ⊥-elim (c refl)

subst-for-same : ∀ {n} (k j : Fin n) -> [ k / j ] k ≡ k
subst-for-same k j with k | k ≟ j
... | ._ | yes refl = refl
... |  _ | no  _    = refl

min-max-≡ : ∀ {n} -> (i j : Fin n) -> min-max i j ≡ (i , j) ⊎ min-max i j ≡ (j , i)
min-max-≡  zero    j      = inj₁ refl
min-max-≡ (suc i)  zero   = inj₂ refl
min-max-≡ (suc i) (suc j) = S.map (cong (P.map suc suc)) (cong (P.map suc suc)) (min-max-≡ i j)

-- Or should (Fin m -> Maybe (Fin m')) be a parameter?
restrict-go : ∀ {n m} -> n ↦ m -> ∃ λ m' -> (n ↦ m') × (Fin m -> Maybe (Fin m'))
restrict-go {0}     f = 0 , id , const nothing
restrict-go {suc n} f =
  let i = f zero
      (m' , r , π) = restrict-go (f ∘ suc)
  in maybe (λ j -> m' , caseFin j r , π)
           (suc m' , caseFin zero (suc ∘ r)
                   , λ j -> if ⌊ j ≟ i ⌋ then just zero else M.map suc (π j))
           (π i)

restrict : ∀ {n m} -> n ↦ m -> ∃ (n ↦_)
restrict = ,_ ∘ proj₁ ∘ proj₂ ∘ restrict-go

coeq : ∀ {n m} -> n ↦ m -> n ↦ m -> m ↦ m
coeq {0}     f g = id
coeq {suc n} f g =
  let (min , max) = min-max (f zero) (g zero)
      r = coeq (f ∘ suc) (g ∘ suc)
  in [ r min / r max ] ∘ r

π : ∀ {n m} -> (f g : n ↦ m) -> m ↦ _
π f g = proj₂ (restrict (coeq f g))

comm : ∀ {n m} -> (f g : n ↦ m) -> coeq f g ∘ f ≗ coeq f g ∘ g
comm {0}     f g  ()
comm {suc n} f g  zero with coeq (f ∘ suc) (g ∘ suc) | f zero | g zero
                          | λ k j -> trans (subst-same k j) (sym (subst-for-same k j))
... | r | i | j | lem with min-max-≡ i j
... | inj₁ p rewrite p = sym (lem (r i) (r j))
... | inj₂ p rewrite p =      lem (r j) (r i)
comm {suc n} f g (suc i) rewrite comm (f ∘ suc) (g ∘ suc) i = refl
