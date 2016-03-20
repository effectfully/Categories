module Categories.Utilities.Replicate where

open import Level using (Lift)
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.Fin hiding (_+_)
open import Data.Product

Replicate : ∀ {α} -> ℕ -> Set α -> Set α
Replicate  0      A = Lift ⊤
Replicate (suc n) A = A × Replicate n A

lookupʳ : ∀ {n α} {A : Set α} -> Fin n -> Replicate n A -> A
lookupʳ  zero   (x , xs) = x
lookupʳ (suc i) (x , xs) = lookupʳ i xs

nlookupʳ : ∀ {m α} {A : Set α} n -> Replicate (ℕ.suc n + m) A -> A
nlookupʳ  0      (x , xs) = x
nlookupʳ (suc n) (x , xs) = nlookupʳ n xs

nlookupʳ₀ : ∀ {α} {A : Set α} n -> Replicate (ℕ.suc n) A -> A
nlookupʳ₀  0      (x , _ ) = x
nlookupʳ₀ (suc n) (x , xs) = nlookupʳ₀ n xs

foldrʳ : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B -> B) -> B -> Replicate n A -> B
foldrʳ {0}     f y  _       = y
foldrʳ {suc n} f y (x , xs) = f x (foldrʳ f y xs)

foldrʳ₁ : ∀ {n α} {A : Set α} -> (A -> A -> A) -> Replicate (ℕ.suc n) A -> A
foldrʳ₁ {0}     f (x , _ ) = x
foldrʳ₁ {suc n} f (x , xs) = f x (foldrʳ₁ f xs)

foldlʳ : ∀ {n α β} {A : Set α} {B : Set β} -> (B -> A -> B) -> B -> Replicate n A -> B
foldlʳ {0}     f y  _       = y
foldlʳ {suc n} f y (x , xs) = foldlʳ f (f y x) xs

foldlʳ₁ : ∀ {n α} {A : Set α} -> (A -> A -> A) -> Replicate (ℕ.suc n) A -> A
foldlʳ₁ f (x , xs) = foldlʳ f x xs
