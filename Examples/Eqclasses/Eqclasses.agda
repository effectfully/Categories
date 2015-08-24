module Categories.Examples.Eqclasses.Eqclasses where

open import Relation.Nullary
open import Data.Nat.Base
open import Data.Fin hiding (#_)
open import Data.Fin.Properties
open import Data.Sum hiding (map)
open import Data.Vec
open import Data.Vec.Properties

open import Categories.Examples.Eqclasses.Utilities
open import Categories.Category hiding (zero; suc; map)

open ≡-Reasoning

List⁺ : ∀ {α} -> Set α -> Set α
List⁺ A = ∃ (Vec A ∘′ suc)

class : ∀ {n m} -> Vec (Fin n) (suc m) -> List⁺ (Fin n)
class = ,_

singleton : ∀ {n} -> Fin n -> List⁺ (Fin n)
singleton = class ∘′ [_]

vec : ∀ {n} -> (c : List⁺ (Fin n)) -> Vec (Fin n) _
vec = proj₂

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

  symmetric : ∀ {i j} -> i ~  j -> j ~ i
  symmetric p = hreflexive (sound reflexive p)

  transitive : ∀ {i j k} -> i ~ j -> j ~ k -> i ~ k
  transitive p q = hreflexive (sound p (symmetric q))

  cosound : ∀ {i j k} -> k ~ i -> k ~ j -> i ≃ j
  cosound p q = sound (symmetric p) (symmetric q)

  glue : ∀ i j -> Vec (Fin n) _
  glue i j = vec (# i) ++ vec (# j)

  glue-∈ : ∀ {k l} i j -> k ~ l -> k ∈ glue i j -> l ∈ glue i j
  glue-∈ i j p q = case ∈-++ (vec (classes ! i)) q of λ
    { (inj₁ r) -> ∈-++₁ (detag (hreflexive (cosound p (tagWith (, i) r))))
    ; (inj₂ r) -> ∈-++₂ (vec (# i)) (detag (hreflexive (cosound p (tagWith (, j) r))))
    }

  glue-∉ : ∀ {k l} i j -> l ~ k -> k ∉ glue i j -> l ∉ glue i j
  glue-∉ i j p c q = c (glue-∈ i j p q)

identity : ∀ {n} -> Classes n
identity = record
  { classes   = classes
  ; reflexive = reflexive
  ; sound     = sound
  } where
      classes = tabulate singleton

      open OnClasses classes

      reflexive : ∀ {i} -> i ~ i
      reflexive {i} = tag (substᶜ (psym (lookup∘tabulate _ i)) here)

      sound : ∀ {i j k} -> i ~ k -> j ~ k -> i ≃ j
      sound {k = k} (tag p) (tag q) rewrite lookup∘tabulate singleton k with p | q
      ... | here     | here     = tag prefl
      ... | here     | there ()
      ... | there () | _

module _ {n} (Cs : Classes n) where
  open Classes Cs renaming (classes to classes₁); open OnClasses₁ classes₁

  merge′ : ∀ i j -> Vec (List⁺ (Fin n)) n
  merge′ i j = classes₁ [ ks ]≔* class ks where ks = glue i j

  module _ i j where
    classes₂ = merge′ i j
    
    open OnClasses₂ classes₂
    
    merge-preserves-∈ : ∀ {k l} -> k ~₁ l -> k ~₂ l
    merge-preserves-∈ {k} {l} p = case [ _≟_ ] l ∈? glue i j of λ
      { (yes q) -> tag (substᶜ (psym (∈-lookup-[]≔* q)) (glue-∈ i j (symmetric p) q))
      ; (no  c) -> tag (substᶜ (psym (∉-lookup-[]≔* c)) (detag p))
      }

    merge-sound : ∀ {i₂ j₂ k₂} -> i₂ ~₂ k₂ -> j₂ ~₂ k₂ -> i₂ ≃₂ j₂
    merge-sound {i₂} {j₂} {k₂} p q = case [ _≟_ ] k₂ ∈? glue i j of λ
      { (yes r) -> tag $
           begin
             #₂ i₂            →⟨ ∈-lookup-[]≔* (substᶜ (∈-lookup-[]≔* r) (detag p)) ⟩
             class (glue i j) ←⟨ ∈-lookup-[]≔* (substᶜ (∈-lookup-[]≔* r) (detag q)) ⟩
             #₂ j₂
           ∎
      ; (no  c) -> let p₁ = tagWith (, k₂) (substᶜ (∉-lookup-[]≔* c) (detag p))
                       p₂ = tagWith (, k₂) (substᶜ (∉-lookup-[]≔* c) (detag q))
                   in tag $
           begin
             #₂ i₂ →⟨ ∉-lookup-[]≔* (glue-∉ i j p₁ c)  ⟩
             #₁ i₂ →⟨ detag (sound p₁ p₂)              ⟩
             #₁ j₂ ←⟨ ∉-lookup-[]≔* (glue-∉ i j p₂ c)  ⟩
             #₂ j₂
           ∎
      }

    ∈₂-merge : j ~₂ i
    ∈₂-merge = tag (substᶜ (psym (∈-lookup-[]≔* (∈-++₁ (detag (reflexiveₑ i)))))
                           (∈-++₂ (vec (#₁ i)) (detag (reflexiveₑ j))))

  merge : ∀ i j -> Classes n
  merge i j = record
    { classes   = merge′ i j
    ; reflexive = merge-preserves-∈ i j reflexive
    ; sound     = merge-sound i j
    }

generateᵃ : ∀ {n m} -> Classes n -> m ↤ n -> m ↤ n -> Classes n
generateᵃ Cs  []      []     = Cs
generateᵃ Cs (i ∷ f) (j ∷ g) = generateᵃ (merge Cs i j) f g

generateᵃ-preserves-∈ : ∀ {n m i j} {Cs : Classes n} (f : m ↤ n) (g : m ↤ n)
                      -> let open Classes
                             open OnClasses₁ (classes  Cs)
                             open OnClasses₂ (classes (generateᵃ Cs f g))
                         in i ~₁ j -> i ~₂ j
generateᵃ-preserves-∈            []      []     p = p
generateᵃ-preserves-∈ {Cs = Cs} (i ∷ f) (j ∷ g) p =
  generateᵃ-preserves-∈ f g (merge-preserves-∈ Cs i j p)

comm-generateᵃ : ∀ {n m} {Cs : Classes n} (f : m ↤ n) (g : m ↤ n)
               -> let open Classes (generateᵃ Cs f g) in classes ‼ f ≡ classes ‼ g
comm-generateᵃ            []      []     = prefl
comm-generateᵃ {Cs = Cs} (i ∷ f) (j ∷ g) =
  cong₂ _∷_ (detag (sound (reflexiveₑ i) (generateᵃ-preserves-∈ f g (∈₂-merge Cs i j))))
            (comm-generateᵃ f g)
    where open Classes (generateᵃ (merge Cs i j) f g); open OnClasses classes

generate : ∀ {n m} -> m ↤ n -> m ↤ n -> Classes n
generate = generateᵃ identity

eqclasses : ∀ {n m} -> m ↤ n -> m ↤ n -> n ↤ n
eqclasses f g = map repr classes
  where open Classes (generate f g)

eqclasses-sound : ∀ {n m} -> (f : m ↤ n) -> (g : m ↤ n) -> eqclasses f g ‼ f ≡ eqclasses f g ‼ g
eqclasses-sound f g =
  begin
    eqclasses f g ‼ f      →⟨ map-cong (flip lookup-map classes) f ⟩
    map (repr ∘′ #) f      →⟨ map-∘ repr # f                       ⟩
    map repr (classes ‼ f) →⟨ cong (map _) (comm-generateᵃ f g)    ⟩
    map repr (classes ‼ g) ←⟨ map-∘ repr # g                       ⟩
    map (repr ∘′ #) g      ←⟨ map-cong (flip lookup-map classes) g ⟩
    eqclasses f g ‼ g
  ∎ where open Classes (generate f g); open OnClasses classes
