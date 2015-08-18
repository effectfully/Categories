open import Categories.Category

module Categories.Functor.Discrete {α β γ} (C : Category α β γ) where

open import Data.Fin public
open import Data.Vec public

open import Categories.Functor
open import Categories.Categories.Discrete

open Category C

D⇒ : ∀ {n} {xs : Vec Obj n} {i j : Fin n} -> i ≡ j -> lookup i xs ⇒ lookup j xs
D⇒ prefl = id

Discreteᶠ : ∀ {n} -> Vec Obj n -> Functor (Discrete (Fin n)) C
Discreteᶠ xs = record
  { F·       = flip lookup xs
  ; F⇒       = D⇒
  ; F-id     = refl
  ; F-∘      = λ {i j k q p} -> F-∘ p q
  ; F-resp-≈ = λ {i j p q} _ -> F-resp-≈ p q
  } where
      F-∘ : ∀ {i j k} -> (p : i ≡ j) -> (q : j ≡ k) -> D⇒ (ptrans p q) ≈ D⇒ q ∘ D⇒ p
      F-∘ prefl prefl = sym idˡ

      F-resp-≈ : ∀ {i j} -> (p q : i ≡ j) -> D⇒ p ≈ D⇒ q
      F-resp-≈ prefl prefl = refl
