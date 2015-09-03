module Categories.Examples.Eqclasses.Eqclasses2 where

open import Function
open import Data.Nat.Base
open import Data.Fin     hiding (_+_; _<_)
open import Data.Maybe.Base renaming (map to _<$>_)
open import Data.Product hiding (zip)
open import Data.Vec     hiding (map)

open import Categories.Examples.Eqclasses.Utilities

infixr 5 _∷_
data IVec {α} (A : ℕ -> Set α) : ℕ -> Set α where
  []  : IVec A 0
  _∷_ : ∀ {n} -> A n -> IVec A n -> IVec A (suc n)

IVecᵈ : ∀ {δ} -> (ℕ -> ℕ -> Set δ) -> ℕ -> Set δ
IVecᵈ D n = IVec (λ i -> D (suc i) n) n

shift : ∀ {δ} -> (ℕ -> ℕ -> Set δ) -> ℕ -> ℕ -> Set δ
shift D j n = D j (suc n)

ilookupᵈ : ∀ {δ n} (D : ℕ -> ℕ -> Set δ) -> (i : Fin n) -> IVecᵈ D n -> D (n ∸ toℕ i) n
ilookupᵈ D  zero   (x ∷ xs) = x
ilookupᵈ D (suc i) (x ∷ xs) = ilookupᵈ (shift D) i xs

iassignᵈ : ∀ {δ n} (D : ℕ -> ℕ -> Set δ) -> (i : Fin n) -> IVecᵈ D n -> D (n ∸ toℕ i) n -> IVecᵈ D n
iassignᵈ D  zero   (x ∷ xs) y = y ∷ xs
iassignᵈ D (suc i) (x ∷ xs) y = x ∷ iassignᵈ (shift D) i xs y

ireplicate : ∀ {n α} {A : ℕ -> Set α} -> (∀ {i} -> A i) -> IVec A n
ireplicate {0}     x = []
ireplicate {suc _} x = x ∷ ireplicate x

forget : ∀ {α β n} {A : ℕ -> Set α} {B : Set β}
       -> (∀ {m} -> Fin n -> A m -> B) -> IVec A n -> Vec B n
forget f  []      = []
forget f (x ∷ xs) = f zero x ∷ forget (f ∘ suc) xs

data [_⋯_⟩ : ℕ -> ℕ -> Set where
  izero : ∀ {n} m -> [ n ∸ m ⋯ suc n ⟩
  isuc  : ∀ {n m} -> [ n ⋯ m ⟩ -> [ n ⋯ suc m ⟩

⟨_⋯_⟩ : ℕ -> ℕ -> Set
⟨ n ⋯ m ⟩ = [ suc n ⋯ m ⟩

ItoFin : ∀ {n m} -> [ n ⋯ m ⟩ -> Fin m
ItoFin (izero _) = zero
ItoFin (isuc  i) = suc (ItoFin i)

Itoℕ : ∀ {n m} -> [ n ⋯ m ⟩ -> ℕ
Itoℕ = toℕ ∘ ItoFin

xor : ∀ {n} -> Fin n -> Fin n -> Maybe (∃ λ (k : Fin n) -> [ n ∸ toℕ k ⋯ n ⟩)
xor  zero    zero   = nothing
xor  zero   (suc j) = just (suc j , izero (toℕ j))
xor (suc i)  zero   = just (suc i , izero (toℕ i))
xor (suc i) (suc j) = map suc isuc <$> xor i j

DAG : ℕ -> Set
DAG n = IVec (λ i -> Maybe ⟨ i ⋯ n ⟩) n

ilookup : ∀ {n} -> (i : Fin n) -> DAG n -> Maybe [ n ∸ toℕ i ⋯ n ⟩
ilookup = ilookupᵈ (λ j n -> Maybe [ j ⋯ n ⟩)

_[_]≔ᵢ_ : ∀ {n} -> DAG n -> (i : Fin n) -> [ n ∸ toℕ i ⋯ n ⟩ -> DAG n
is [ i ]≔ᵢ j = iassignᵈ (λ j n -> Maybe [ j ⋯ n ⟩) i is (just j)

-- Terminates being closed.
{-# NON_TERMINATING #-}
ilookup* : ∀ {n} -> Fin n -> DAG n -> Fin n
ilookup* i is = maybe (λ j -> ilookup* (ItoFin j) is) i (ilookup i is)

step : ∀ {n} -> Fin n -> Fin n -> DAG n -> DAG n
step i j is = maybe (uncurry (is [_]≔ᵢ_)) is (xor (ilookup* i is) (ilookup* j is))

eqclasses : ∀ {n m} -> n ↤ m -> n ↤ m -> m ↤ m
eqclasses f g = forget (maybe′ ItoFin) (zipfoldr _ step (ireplicate nothing) f g)
