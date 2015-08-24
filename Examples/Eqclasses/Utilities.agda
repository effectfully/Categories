module Categories.Examples.Eqclasses.Utilities where

open import Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat.Base
open import Data.Fin
open import Data.Fin.Properties
open import Data.Sum as Sum
open import Data.Product
open import Data.Vec as Vec
open import Data.Vec.Properties

infixl 7 _!_ _‼_
infixl 6 _[_]≔*_
infix  4 _∉_

_↤_ : ℕ -> ℕ -> Set
n ↤ m = Vec (Fin m) n

_!_ : ∀ {α n} {A : Set α} -> Vec A n -> Fin n -> A
_!_ = flip lookup

_‼_ : ∀ {α n m} {A : Set α} -> Vec A n -> m ↤ n -> Vec A m
xs ‼ is = Vec.map (xs !_) is

_[_]≔*_ : ∀ {α n m} {A : Set α} -> Vec A n -> m ↤ n -> A -> Vec A n
xs [ is ]≔* x = foldr _ (λ i rs -> rs [ i ]≔ x) xs is

∈-++₁ : ∀ {α n m} {A : Set α} {xs : Vec A n} {ys : Vec A m} {x}
      -> x ∈ xs -> x ∈ xs ++ ys
∈-++₁  here     = here
∈-++₁ (there p) = there (∈-++₁ p)

∈-++₂ : ∀ {α n m} {A : Set α} {ys : Vec A m} {x}
      -> (xs : Vec A n) -> x ∈ ys -> x ∈ xs ++ ys
∈-++₂  []      p = p
∈-++₂ (x ∷ xs) p = there (∈-++₂ xs p)

∈-++ : ∀ {α n m} {A : Set α} {ys : Vec A m} {x} -> (xs : Vec A n)
     -> x ∈ xs ++ ys -> x ∈ xs ⊎ x ∈ ys
∈-++  []       p        = inj₂ p
∈-++ (x ∷ xs)  here     = inj₁ here
∈-++ (x ∷ xs) (there p) = Sum.map there id (∈-++ xs p)

_∉_ : ∀ {α n} {A : Set α} -> A -> Vec A n -> Set α
x ∉ xs = ¬ (x ∈ xs)

_∘∉_ : ∀ {α n} {A : Set α} {x y} {xs : Vec A n} -> x ≢ y -> x ∉ xs -> x ∉ y ∷ xs
_∘∉_ p q  here     = p refl
_∘∉_ p q (there r) = q r

∉-inj : ∀ {α n} {A : Set α} {x y} {xs : Vec A n} -> x ∉ y ∷ xs -> x ≢ y × x ∉ xs
∉-inj c = (λ p -> subst (λ x -> _ ∉ x ∷ _) (sym p) c here) , c ∘′ there

[_]_∈?_ : ∀ {α n} {A : Set α}
        -> Decidable (_≡_ {A = A}) -> Decidable (λ x (xs : Vec A n) -> x ∈ xs)
[ _≟_ ] y ∈?  []      = no λ()
[ _≟_ ] y ∈? (x ∷ xs) with y ≟ x
... | yes p rewrite p = yes here
... | no  p with [ _≟_ ] y ∈? xs
... | yes q = yes (there q)
... | no  q = no  (p ∘∉ q)

∈-lookup-[]≔* : ∀ {α n m} {A : Set α} {xs : Vec A n} {is : m ↤ n} {i x}
              -> i ∈ is -> lookup i (xs [ is ]≔* x) ≡ x
∈-lookup-[]≔* {is = i ∷ is}      here     = lookup∘update i (_ [ is ]≔* _) _
∈-lookup-[]≔* {is = i ∷ is} {j} (there p) with i | j ≟ i
... | ._ | yes refl = lookup∘update j (_ [ is ]≔* _) _
... |  _ | no  c    = trans (lookup∘update′ c _ _) (∈-lookup-[]≔* p)

∉-lookup-[]≔* : ∀ {α n m} {A : Set α} {xs : Vec A n} {is : m ↤ n} {i x}
              -> i ∉ is -> lookup i (xs [ is ]≔* x) ≡ lookup i xs
∉-lookup-[]≔* {is = []    } c = refl
∉-lookup-[]≔* {is = i ∷ is} c = trans (lookup∘update′ (proj₁ (∉-inj c)) _ _)
                                      (∉-lookup-[]≔* (proj₂ (∉-inj c)))

lookup-map : ∀ {α β n} {A : Set α} {B : Set β} {f : A -> B}
           -> ∀ i -> (xs : Vec A n) -> lookup i (Vec.map f xs) ≡ f (lookup i xs)
lookup-map  zero   (x ∷ xs) = refl
lookup-map (suc i) (x ∷ xs) = lookup-map i xs

map-[]≔* : ∀ {α β n m} {A : Set α} {B : Set β} {f : A -> B} {xs : Vec A n} {x}
         -> (is : m ↤ n) -> Vec.map f (xs [ is ]≔* x) ≡ Vec.map f xs [ is ]≔* f x
map-[]≔* {f = f} {xs} = foldr-fusion xs (Vec.map f) (λ i r -> map-[]≔ f r i)
