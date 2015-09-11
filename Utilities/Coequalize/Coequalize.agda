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

unjust : ∀ {α} {A : Set α} {x y : A} -> _≡_ {A = Maybe A} (just x) (just y) -> x ≡ y
unjust refl = refl

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

subst-same : ∀ {n} -> (k j : Fin n) -> [ k / j ] j ≡ k
subst-same k j with j ≟ j
... | yes _ = refl
... | no  c = ⊥-elim (c refl)

subst-for-same : ∀ {n} -> (k j : Fin n) -> [ k / j ] k ≡ k
subst-for-same k j with k | k ≟ j
... | ._ | yes refl = refl
... |  _ | no  _    = refl

min-max-≡ : ∀ {n} -> (i j : Fin n) -> min-max i j ≡ (i , j) ⊎ min-max i j ≡ (j , i)
min-max-≡  zero    j      = inj₁ refl
min-max-≡ (suc i)  zero   = inj₂ refl
min-max-≡ (suc i) (suc j) = S.map (cong (P.map suc suc)) (cong (P.map suc suc)) (min-max-≡ i j)

restrict-go : ∀ {n m} -> n ↦ m -> ∃ λ m' -> (n ↦ m') × (Fin m -> Maybe (Fin m'))
restrict-go {0}     f = 0 , id , const nothing
restrict-go {suc n} f =
  let i = f zero
      (m' , r , π) = restrict-go (f ∘ suc)
  in maybe (λ j -> m' , caseFin j r , π)
           (suc m' , caseFin zero (suc ∘ r)
                   , λ j -> if ⌊ j ≟ i ⌋ then just zero else M.map suc (π j))
           (π i)

project : ∀ {n m} -> (f : n ↦ m) -> Fin m -> Maybe (Fin _)
project = proj₂ ∘ proj₂ ∘ restrict-go

restrict : ∀ {n m} -> (f : n ↦ m) -> n ↦ _
restrict = proj₁ ∘ proj₂ ∘ restrict-go

invert-restrict : ∀ {n m} -> (f : n ↦ m) -> ∃ λ s -> restrict f ∘ s ≗ id
invert-restrict {0}     f = id , λ {()}
invert-restrict {suc n} f with restrict-go (f ∘ suc) | invert-restrict (f ∘ suc)
... | _ , _ , π | s , p with π (f zero)
... | just  j = suc ∘ s , p
... | nothing = caseFin zero (suc ∘ s) , caseFin refl (cong suc ∘ p)

project-restrict : ∀ {n m} -> (f : n ↦ m) -> project f ∘ f ≗ just ∘ restrict f
project-restrict {0}     f  ()
project-restrict {suc n} f  zero   with restrict-go (f ∘ suc)
... | _ , _ , π with π (f zero) | inspect π (f zero)
... | just  j | [ q ] = q
... | nothing | [ q ] with f zero ≟ f zero
... | yes r = refl
... | no  c = ⊥-elim (c refl)
project-restrict {suc n} f (suc i) with restrict-go (f ∘ suc) | project-restrict (f ∘ suc) i
... | _ , _ , π | p with π (f zero) | inspect π (f zero)
... | just  j | [ q ] = p
... | nothing | [ q ] with f (suc i) ≟ f zero
... | yes r rewrite r | q = case p of λ()
... | no  c rewrite p = refl

restrict-preserves-≡ : ∀ {n m i j} -> (f : n ↦ m) -> f i ≡ f j -> restrict f i ≡ restrict f j
restrict-preserves-≡ {i = i} {j = j} f p = let open ≡-Reasoning in unjust $
  begin
    just (restrict f i) ≡⟨ sym (project-restrict f i) ⟩
    project f (f i)     ≡⟨ cong (project f) p         ⟩
    project f (f j)     ≡⟨      project-restrict f j  ⟩
    just (restrict f j)
  ∎
  
coeq : ∀ {n m} -> n ↦ m -> n ↦ m -> m ↦ m
coeq {0}     f g = id
coeq {suc n} f g =
  let (min , max) = min-max (f zero) (g zero)
      r = coeq (f ∘ suc) (g ∘ suc)
  in [ r min / r max ] ∘ r

coeq-comm : ∀ {n m} -> (f g : n ↦ m) -> coeq f g ∘ f ≗ coeq f g ∘ g
coeq-comm {0}     f g  ()
coeq-comm {suc n} f g  zero with coeq (f ∘ suc) (g ∘ suc) | f zero | g zero
                          | λ k j -> trans (subst-same k j) (sym (subst-for-same k j))
... | r | i | j | lem with min-max-≡ i j
... | inj₁ p rewrite p = sym (lem (r i) (r j))
... | inj₂ p rewrite p =      lem (r j) (r i)
coeq-comm {suc n} f g (suc i) rewrite coeq-comm (f ∘ suc) (g ∘ suc) i = refl
