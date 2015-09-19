module Categories.Utilities.Coequalize.Coequalize where

open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (module ≡-Reasoning)
open import Data.Empty
open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Fin
open import Data.Fin.Properties
open import Data.Maybe.Base as M
open import Data.Sum        as S
open import Data.Product    as P

open import Categories.Setoid.Instances using (module ≡-Reasoning)
open ≡-Reasoning

-- Utilities.

unJust : ∀ {α} {A : Set α} {x y : A} -> _≡_ {A = Maybe A} (just x) (just y) -> x ≡ y
unJust refl = refl

fromMapJust : ∀ {α β} {A : Set α} {B : Set β} {f : A -> B} {y}
            -> ∀ mx -> M.map f mx ≡ just y -> A
fromMapJust  nothing ()
fromMapJust (just x) p  = x

unMapJust : ∀ {α β} {A : Set α} {B : Set β} {f : A -> B} {y}
          -> ∀ mx -> (p : M.map f mx ≡ just y) -> f (fromMapJust mx p) ≡ y
unMapJust  nothing ()
unMapJust (just x) refl = refl

≟-refl : ∀ {α} {A : Set α} (_≟_ : Decidable (_≡_ {A = A})) x -> (x ≟ x) ≡ yes refl 
≟-refl _≟_ x with x ≟ x
... | yes refl = refl
... | no  c    = ⊥-elim (c refl)

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
subst-same k j rewrite ≟-refl _≟_ j = refl

subst-for-same : ∀ {n} -> (k j : Fin n) -> [ k / j ] k ≡ k
subst-for-same k j with k | k ≟ j
... | ._ | yes refl = refl
... |  _ | no  _    = refl

min-max-≡ : ∀ {n} -> (i j : Fin n) -> min-max i j ≡ (i , j) ⊎ min-max i j ≡ (j , i)
min-max-≡  zero    j      = inj₁ refl
min-max-≡ (suc i)  zero   = inj₂ refl
min-max-≡ (suc i) (suc j) = S.map (cong (P.map suc suc)) (cong (P.map suc suc)) (min-max-≡ i j)

-- Restricting.

restrict-rename : ∀ {n m} -> n ↦ m -> ∃ λ m' -> (n ↦ m') × (Fin m -> Maybe (Fin m'))
restrict-rename {0}     f = 0 , id , const nothing
restrict-rename {suc n} f =
  let i = f zero
      (m' , r , π) = restrict-rename (f ∘ suc)
  in maybe (λ j -> m' , caseFin j r , π)
           (suc m' , caseFin zero (suc ∘ r)
                   , λ j -> if ⌊ i ≟ j ⌋ then just zero else M.map suc (π j))
           (π i)

rename : ∀ {n m} -> (f : n ↦ m) -> Fin m -> Maybe (Fin _)
rename = proj₂ ∘ proj₂ ∘ restrict-rename

restrict : ∀ {n m} -> (f : n ↦ m) -> n ↦ _
restrict = proj₁ ∘ proj₂ ∘ restrict-rename

invert-restrict : ∀ {n m} -> (f : n ↦ m) -> ∃ λ s -> restrict f ∘ s ≗ id
invert-restrict {0}     f = id , λ()
invert-restrict {suc n} f with restrict-rename (f ∘ suc) | invert-restrict (f ∘ suc)
... | _ , _ , π | s , p with π (f zero)
... | just  j = suc ∘ s , p
... | nothing = caseFin zero (suc ∘ s) , caseFin refl (cong suc ∘ p)

rename≗restrict : ∀ {n m} -> (f : n ↦ m) -> rename f ∘ f ≗ just ∘ restrict f
rename≗restrict {0}     f  ()
rename≗restrict {suc n} f  zero   with restrict-rename (f ∘ suc)
... | _ , _ , π with π (f zero) | inspect π (f zero)
... | just  j | [ q ] = q
... | nothing | [ q ] rewrite ≟-refl _≟_ (f zero) = refl
rename≗restrict {suc n} f (suc i) with restrict-rename (f ∘ suc) | rename≗restrict (f ∘ suc) i
... | _ , _ , π | p with π (f zero) | inspect π (f zero)
... | just  j | [ q ] = p
... | nothing | [ q ] with f zero ≟ f (suc i)
... | yes r rewrite r | q = case p of λ()
... | no  c rewrite p     = refl

rename-injective : ∀ {n m i j} (f : n ↦ m)
                 -> rename f i ≡ rename f j -> rename f i ≡ nothing ⊎ i ≡ j
rename-injective {0}                     f p = inj₁ refl
rename-injective {suc n} {i = i} {j = j} f p
    with rename (f ∘ suc) | rename-injective {i = i} {j = j} (f ∘ suc)
... | π | r with π (f zero)
... | just  k = r p
... | nothing with f zero ≟ i | f zero ≟ j
... | yes q₁ | yes q₂ = inj₂ (trans (sym q₁) q₂)
... | yes _  | no  _  = case unMapJust (π j) (sym p) of λ()
... | no  _  | yes _  = case unMapJust (π i)      p  of λ()
... | no  _  | no  _  with π i
... | nothing = inj₁ refl
... | just l  with π j
... | nothing = case p of λ()
... | just _  with l | p
... | ._ | refl = S.map (λ()) id (r refl)

restrict-to-rename : ∀ {n m i j} (f : n ↦ m)
                   -> restrict f i ≡ restrict f j -> rename f (f i) ≡ rename f (f j)
restrict-to-rename {i = i} {j = j} f p =
  begin
    rename f (f i)      →⟨ rename≗restrict f i ⟩
    just (restrict f i) →⟨ cong just p         ⟩
    just (restrict f j) ←⟨ rename≗restrict f j ⟩
    rename f (f j)
  ∎

rename-to-restrict : ∀ {n m i j} (f : n ↦ m)
                   -> rename f (f i) ≡ rename f (f j) -> restrict f i ≡ restrict f j
rename-to-restrict {i = i} {j = j} f p = unJust $
  begin
    just (restrict f i) ←⟨ rename≗restrict f i ⟩
    rename f (f i)      →⟨ p                   ⟩
    rename f (f j)      →⟨ rename≗restrict f j ⟩
    just (restrict f j)
  ∎

restrict-preserves-≡ : ∀ {n m i j} (f : n ↦ m)
                     -> f i ≡ f j -> restrict f i ≡ restrict f j
restrict-preserves-≡ {i = i} {j = j} f p = rename-to-restrict f (cong (rename f) p)

restrict-reflects-≡ : ∀ {n m i j} (f : n ↦ m)
                    -> restrict f i ≡ restrict f j -> f i ≡ f j
restrict-reflects-≡ f p = case rename-injective f (restrict-to-rename f p) of λ
  { (inj₁ q) -> case trans (sym (rename≗restrict f _)) q of λ()
  ; (inj₂ q) -> q
  }

-- Coequalizing.

coeq : ∀ {n m} -> n ↦ m -> n ↦ m -> m ↦ m
coeq {0}     f g = id
coeq {suc n} f g =
  let (min , max) = min-max (f zero) (g zero)
      r = coeq (f ∘ suc) (g ∘ suc)
  in [ r min / r max ] ∘ r

coeq-comm : ∀ {n m} -> (f g : n ↦ m) -> coeq f g ∘ f ≗ coeq f g ∘ g
coeq-comm {0}     f g  ()
coeq-comm {suc n} f g  zero
    with coeq (f ∘ suc) (g ∘ suc) | f zero | g zero
       | λ k j -> trans (subst-same k j) (sym (subst-for-same k j))
... | r | i | j | lem with min-max-≡ i j
... | inj₁ p rewrite p = sym (lem (r i) (r j))
... | inj₂ p rewrite p =      lem (r j) (r i)
coeq-comm {suc n} f g (suc i) rewrite coeq-comm (f ∘ suc) (g ∘ suc) i = refl

coeq-univ : ∀ {n m p} {f g : n ↦ m} -> (u : m ↦ p) -> u ∘ f ≗ u ∘ g -> u ∘ coeq f g ≗ u
coeq-univ {0}                     u p x = refl
coeq-univ {suc n} {f = f} {g = g} u p x with f zero | g zero | p zero
... | i | j | p' with min-max i j | min-max-≡ i j | coeq (f ∘ suc) (g ∘ suc) | coeq-univ u (p ∘ suc)
... | min , max | mm | r | q with r x ≟ r max
... | no  _ = q x
... | yes s with λ i j p' s ->
        begin
          u (r i) →⟨ q i      ⟩
          u  i    →⟨ p'       ⟩
          u  j    ←⟨ q j      ⟩
          u (r j) ←⟨ cong u s ⟩
          u (r x) →⟨ q x      ⟩
          u  x
        ∎
... | lem with min | max | mm
... | ._ | ._ | inj₁ refl = lem i j      p'  s
... | ._ | ._ | inj₂ refl = lem j i (sym p') s
