module Categories.Examples.Eqclasses.Eqclasses where

open import Relation.Nullary
open import Data.Nat.Base
open import Data.Fin hiding (#_)
open import Data.Fin.Properties
open import Data.Sum hiding (map)
open import Data.Vec
open import Data.Vec.Properties

open import Categories.Utilities.Prelude hiding (suc; map)
open import Categories.Examples.Eqclasses.Utilities
open import Categories.Setoid

open ≡-Reasoning

List⁺ : ∀ {α} -> Set α -> Set α
List⁺ A = ∃ (Vec A ∘′ suc)

class : ∀ {n m} -> Vec (Fin n) (suc m) -> List⁺ (Fin n)
class = ,_

vec : ∀ {n} -> (c : List⁺ (Fin n)) -> Vec (Fin n) _
vec = proj₂

sing : ∀ {n} -> Fin n -> List⁺ (Fin n)
sing = class ∘′ [_]

repr : ∀ {n} -> List⁺ (Fin n) -> Fin n
repr = head ∘′ vec

infix 4 _∈ᶜ_
_∈ᶜ_ : ∀ {n} -> Fin n -> List⁺ (Fin n) -> Set
i ∈ᶜ c = i ∈ vec c 

substᶜ : ∀ {n} {i : Fin n} {c d : List⁺ (Fin n)} -> c ≡ d -> i ∈ᶜ c -> i ∈ᶜ d
substᶜ prefl = id′

module OnClasses {n} (classes : Vec (List⁺ (Fin n)) n) where
  infix 4 _~_ _≃_

  _~_ : Fin n -> Fin n -> Set
  _~_ = Tag₂ λ i j -> i ∈ᶜ classes ! j

  _≃_ : Fin n -> Fin n -> Set
  _≃_ = Tag₂ λ i j -> classes ! i ≡ classes ! j

  # : ∀ i -> List⁺ (Fin n)
  # i = classes ! i

module OnClasses₁ {n} (classes : Vec (List⁺ (Fin n)) n) =
  OnClasses classes renaming (_~_ to _~₁_; _≃_ to _≃₁_; # to #₁)

module OnClasses₂ {n} (classes : Vec (List⁺ (Fin n)) n) =
  OnClasses classes renaming (_~_ to _~₂_; _≃_ to _≃₂_; # to #₂)

record Classes n : Set where
  field
    classes : Vec (List⁺ (Fin n)) n

  open OnClasses classes

  field
    reflexive : ∀ {i} -> i ~ i
    sound     : ∀ {i j k} -> i ~ k -> j ~ k -> i ≃ j

  reflexiveₑ : ∀ i -> i ~ i
  reflexiveₑ _ = reflexive

  hreflexive : ∀ {i j} -> i ≃ j -> i ~ j
  hreflexive (tag p) = tag (substᶜ p (detag reflexive))

  symmetric : ∀ {i j} -> i ~ j -> j ~ i
  symmetric p = hreflexive (sound reflexive p)

  transitive : ∀ {i j k} -> i ~ j -> j ~ k -> i ~ k
  transitive p q = hreflexive (sound p (symmetric q))

  cosound : ∀ {i j k} -> k ~ i -> k ~ j -> i ≃ j
  cosound p q = sound (symmetric p) (symmetric q)

  module Glue i j where
    glued : Vec (Fin n) _
    glued = vec (# i) ++ vec (# j)

    glued-∈ : ∀ {k l} -> k ~ l -> k ∈ glued -> l ∈ glued
    glued-∈ p q = case ∈-++ (vec (# i)) q of λ
      { (inj₁ r) -> ∈-++₁             (detag (hreflexive (cosound p (tagWith (, i) r))))
      ; (inj₂ r) -> ∈-++₂ (vec (# i)) (detag (hreflexive (cosound p (tagWith (, j) r))))
      }

    glued-∉ : ∀ {k l} -> l ~ k -> k ∉ glued -> l ∉ glued
    glued-∉ p c q = c (glued-∈ p q)

identity : ∀ {n} -> Classes n
identity = record
  { classes   = classes
  ; reflexive = reflexive
  ; sound     = sound
  } where
      classes = tabulate sing

      open OnClasses classes

      reflexive : ∀ {i} -> i ~ i
      reflexive {i} = tag (substᶜ (psym (lookup∘tabulate _ i)) here)

      sound : ∀ {i j k} -> i ~ k -> j ~ k -> i ≃ j
      sound {k = k} (tag p) (tag q) rewrite lookup∘tabulate sing k with p | q
      ... | here     | here     = tag prefl
      ... | here     | there ()
      ... | there () | _

module Merge {n} (Cs : Classes n) (i j : Fin n) where
  open Classes Cs renaming (classes to classes₁)
  open Glue i j

  classes₂ : Vec (List⁺ (Fin n)) n
  classes₂ = classes₁ [ glued ]≔* class glued

  open OnClasses₁ classes₁
  open OnClasses₂ classes₂
    
  merge-preserves-∈ : ∀ {k l} -> k ~₁ l -> k ~₂ l
  merge-preserves-∈ {k} {l} p = case [ _≟_ ] l ∈? glued of λ
    { (yes q) -> tag (substᶜ (psym (∈-lookup-[]≔* q)) (glued-∈ (symmetric p) q))
    ; (no  c) -> tag (substᶜ (psym (∉-lookup-[]≔* c)) (detag p))
    }

  merge-reflects-∉ : ∀ {k l} -> l ∉ glued -> k ~₂ l -> k ~₁ l
  merge-reflects-∉ c p = tag (substᶜ (∉-lookup-[]≔* c) (detag p))

  merge-glues : ∀ {k l} -> l ∈ glued -> k ~₂ l -> #₂ k ≡ class glued
  merge-glues p q = ∈-lookup-[]≔* (substᶜ (∈-lookup-[]≔* p) (detag q))

  merge-ignores : ∀ {k l} -> l ∉ glued -> k ~₁ l -> #₂ k ≡ #₁ k
  merge-ignores c p = ∉-lookup-[]≔* (glued-∉ p c)

  merge-sound : ∀ {i₂ j₂ k₂} -> i₂ ~₂ k₂ -> j₂ ~₂ k₂ -> i₂ ≃₂ j₂
  merge-sound {i₂} {j₂} {k₂} p₂ q₂ = case [ _≟_ ] k₂ ∈? glued of λ
    { (yes r) -> tag $
         begin
           #₂ i₂       →⟨ merge-glues r p₂ ⟩
           class glued ←⟨ merge-glues r q₂ ⟩
           #₂ j₂
         ∎
    ; (no  c) -> let p₁ = merge-reflects-∉ c p₂
                     q₁ = merge-reflects-∉ c q₂
                 in tag $
         begin
           #₂ i₂ →⟨ merge-ignores c p₁  ⟩
           #₁ i₂ →⟨ detag (sound p₁ q₁) ⟩
           #₁ j₂ ←⟨ merge-ignores c q₁  ⟩
           #₂ j₂
         ∎
    }

  ∈₂-merge : j ~₂ i
  ∈₂-merge = tag (substᶜ (psym (∈-lookup-[]≔* (∈-++₁ (detag (reflexiveₑ i)))))
                         (∈-++₂ (vec (#₁ i)) (detag (reflexiveₑ j))))
    
  merged : Classes n
  merged = record
    { classes   = classes₂
    ; reflexive = merge-preserves-∈ reflexive
    ; sound     = merge-sound
    }

generateᵃ : ∀ {n m} -> Classes n -> m ↤ n -> m ↤ n -> Classes n
generateᵃ Cs  []      []     = Cs
generateᵃ Cs (i ∷ f) (j ∷ g) = generateᵃ merged f g
  where open Merge Cs i j

generateᵃ-preserves-∈ : ∀ {n m i j} {Cs : Classes n} (f : m ↤ n) (g : m ↤ n)
                      -> let open Classes
                             open OnClasses₁ (classes  Cs)
                             open OnClasses₂ (classes (generateᵃ Cs f g))
                         in i ~₁ j -> i ~₂ j
generateᵃ-preserves-∈            []      []     p = p
generateᵃ-preserves-∈ {Cs = Cs} (i ∷ f) (j ∷ g) p = generateᵃ-preserves-∈ f g (merge-preserves-∈ p)
  where open Merge Cs i j

generateᵃ-sound : ∀ {n m} {Cs : Classes n} (f : m ↤ n) (g : m ↤ n)
               -> let open Classes (generateᵃ Cs f g) in classes ‼ f ≡ classes ‼ g
generateᵃ-sound            []      []     = prefl
generateᵃ-sound {Cs = Cs} (i ∷ f) (j ∷ g) =
  cong₂ _∷_ (detag (sound (reflexiveₑ i) (generateᵃ-preserves-∈ f g ∈₂-merge)))
            (generateᵃ-sound f g)
    where open Merge Cs i j
          open Classes (generateᵃ merged f g)

generate : ∀ {n m} -> m ↤ n -> m ↤ n -> Classes n
generate = generateᵃ identity

eqclasses : ∀ {n m} -> m ↤ n -> m ↤ n -> n ↤ n
eqclasses f g = map repr classes
  where open Classes (generate f g)

eqclasses-sound : ∀ {n m} -> (f : m ↤ n) -> (g : m ↤ n) -> eqclasses f g ‼ f ≡ eqclasses f g ‼ g
eqclasses-sound f g =
  begin
    map repr classes ‼ f   →⟨ map-cong (flip lookup-map classes) f ⟩
    map (repr ∘′ #) f      →⟨ map-∘ repr # f                       ⟩
    map repr (classes ‼ f) →⟨ cong (map _) (generateᵃ-sound f g)   ⟩
    map repr (classes ‼ g) ←⟨ map-∘ repr # g                       ⟩
    map (repr ∘′ #) g      ←⟨ map-cong (flip lookup-map classes) g ⟩
    map repr classes ‼ g
  ∎ where open Classes (generate f g)
          open OnClasses classes
