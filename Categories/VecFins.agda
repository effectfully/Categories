module Categories.Categories.VecFins where

open import Data.Nat.Base
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Vec.Properties

open import Categories.Category hiding (suc) renaming (zero to lzero; map to pmap)

open ≡-Reasoning

infix  4 _↤_
infixl 7 _!_ _‼_

_↤_ : ℕ -> ℕ -> Set
n ↤ m = Vec (Fin m) n

_!_ : ∀ {α n} {A : Set α} -> Vec A n -> Fin n -> A
_!_ = flip lookup

_‼_ : ∀ {α n m} {A : Set α} -> Vec A n -> m ↤ n -> Vec A m
xs ‼ is = map (xs !_) is

Fins : Category lzero lzero lzero
Fins = record
  { Obj      = ℕ
  ; _⇒_      = _↤_
  ; setoid   = ≡-ISetoid
  ; id       = allFin _
  ; _∘_      = _‼_
  ; idˡ      = ptrans (map-cong lookup-allFin _) (map-id _)
  ; idʳ      = map-lookup-allFin _
  ; assoc    = assoc
  ; ∘-resp-≈ = cong₂ _‼_
  } where
      assoc : ∀ {n m p q} {h : p ↤ q} {g : m ↤ p} {f : n ↤ m} -> (h ‼ g) ‼ f ≡ h ‼ (g ‼ f) 
      assoc {f = []   } = prefl
      assoc {f = i ∷ _} = cong₂ _∷_ (‼-! i) assoc where
        ‼-! : ∀ {n m p} {g : m ↤ p} {f : n ↤ m} -> ∀ i -> (g ‼ f) ! i ≡ g ! (f ! i)
        ‼-! {f = []   }  ()
        ‼-! {f = _ ∷ _}  zero   = prefl
        ‼-! {f = _ ∷ _} (suc i) = ‼-! i

open import Categories.Object Fins

initial : Initial
initial = record
  { Ob     = 0
  ; ↜      = []
  ; ↜-univ = λ{ {_} {[]} -> prefl }
  }

binaryCoproducts : BinaryCoproducts
binaryCoproducts {n} {m} = record
  { Ob      = n + m
  ; ι¹      = map (inject+ m) (allFin n)
  ; ι²      = map (raise   n) (allFin m)
  ; [_,_]   = _++_
  ; []-inj  = ++-injective _ _
  ; []-univ = []-univ
  } where
      ++-injective : ∀ {α n m} {A : Set α} {ys₁ ys₂ : Vec A m} (xs₁ xs₂ : Vec A n)
                   -> xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ -> xs₁ ≡ xs₂ ×ₚ ys₁ ≡ ys₂
      ++-injective  []         []        p = prefl , p
      ++-injective (x₁ ∷ xs₁) (x₂ ∷ xs₂) p =
        case ∷-injective p of λ{ (q , r) ->
            case ++-injective xs₁ xs₂ r of λ{ (s , t) ->
                cong₂ _∷_ q s , t
              }
          }

      tabulate-++ : ∀ n {m α} {A : Set α} (xs : Vec A (n + m))
                  ->    tabulate ((xs !_) ∘′ inject+ {n} m)
                     ++ tabulate ((xs !_) ∘′ raise n)
                      ≡ xs
      tabulate-++  zero    xs      = tabulate∘lookup xs
      tabulate-++ (suc n) (x ∷ xs) = cong (x ∷_) (tabulate-++ n xs)

      map-map-tabulate : ∀ {α β γ n} {A : Set α} {B : Set β} {C : Set γ}
                           {xs} {h : B -> C} {g : A -> B} {f : Fin n -> A}
                       -> map h (map g (tabulate f)) ≡ xs -> tabulate (h ∘′ g ∘′ f) ≡ xs
      map-map-tabulate {xs = xs} {h} {g} {f} p =
        begin
          tabulate (h ∘′ g ∘′ f)     →⟨ tabulate-∘ h (g ∘′ f)         ⟩
          map h (tabulate (g ∘′ f))  →⟨ cong (map h) (tabulate-∘ g f) ⟩
          map h (map g (tabulate f)) →⟨ p                             ⟩
          xs
        ∎

      []-univ : ∀ {n m p} {f : n ↤ p} {g : m ↤ p} {u : n + m ↤ p}
              -> map (u !_) (map (inject+ m) (allFin n)) ≡ f
              -> map (u !_) (map (raise   n) (allFin m)) ≡ g
              -> f ++ g ≡ u
      []-univ {n} {m} {p} {f} {g} {u} q r =
        begin
          f ++ g                           ←⟨ cong (_++ _)              (map-map-tabulate q) ⟩
          tabulate {n} _ ++ g              ←⟨ cong (tabulate {n} _ ++_) (map-map-tabulate r) ⟩
          tabulate {n} _ ++ tabulate {m} _ →⟨ tabulate-++ n _                                ⟩
          u
        ∎
