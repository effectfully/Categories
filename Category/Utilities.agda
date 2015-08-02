module Categories.Category.Utilities where

open import Categories.Category.Category

module Utilities {α β γ} (C : Category α β γ) where

  ∘-resp-≈ˡ : ∀ {A B C} {g : B ⇒ C} {f₁ f₂ : A ⇒ B} -> f₁ ≈ f₂ -> g ∘ f₁ ≈ g ∘ f₂
  ∘-resp-≈ˡ p = ∘-resp-≈ refl p

  ∘-resp-≈ʳ : ∀ {A B C} {g₁ g₂ : B ⇒ C} {f : A ⇒ B} -> g₁ ≈ g₂ -> g₁ ∘ f ≈ g₂ ∘ f
  ∘-resp-≈ʳ p = ∘-resp-≈ p refl

  reassocˡ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
           -> (h ∘ g) ∘ f ≈ i -> h ∘ g ∘ f ≈ i
  reassocˡ = right assoc

  reassocʳ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
           -> i ≈ (h ∘ g) ∘ f -> i ≈ h ∘ g ∘ f
  reassocʳ = flip trans assoc

  reassoc² : ∀ {A B₁ B₂ C₁ C₂ D} {h₁ : C₁ ⇒ D} {h₂ : C₂ ⇒ D}
               {g₁ : B₁ ⇒ C₁} {g₂ : B₂ ⇒ C₂} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
           -> (h₁ ∘ g₁) ∘ f₁ ≈ (h₂ ∘ g₂) ∘ f₂ -> h₁ ∘ g₁ ∘ f₁ ≈ h₂ ∘ g₂ ∘ f₂
  reassoc² = assoc ⌈_⌉ assoc

  unreassocˡ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
             -> h ∘ g ∘ f ≈ i -> (h ∘ g) ∘ f ≈ i
  unreassocˡ = trans assoc

  unreassocʳ : ∀ {A B C D} {h : C ⇒ D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ D}
             -> i ≈ h ∘ g ∘ f -> i ≈ (h ∘ g) ∘ f
  unreassocʳ = flip left assoc

  unreassoc² : ∀ {A B₁ B₂ C₁ C₂ D} {h₁ : C₁ ⇒ D} {h₂ : C₂ ⇒ D}
                 {g₁ : B₁ ⇒ C₁} {g₂ : B₂ ⇒ C₂} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
             -> h₁ ∘ g₁ ∘ f₁ ≈ h₂ ∘ g₂ ∘ f₂ -> (h₁ ∘ g₁) ∘ f₁ ≈ (h₂ ∘ g₂) ∘ f₂
  unreassoc² = assoc ⌊_⌋ assoc

  ∘ˡ-resp-≈ˡ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : C ⇒ D} 
             -> g ∘ f ≈ i -> (h ∘ g) ∘ f ≈ h ∘ i
  ∘ˡ-resp-≈ˡ = unreassocˡ ∘′ ∘-resp-≈ˡ

  ∘ʳ-resp-≈ˡ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : C ⇒ D} 
             -> i ≈ g ∘ f -> h ∘ i ≈ (h ∘ g) ∘ f
  ∘ʳ-resp-≈ˡ = unreassocʳ ∘′ ∘-resp-≈ˡ

  ∘²-resp-≈ˡ : ∀ {A B₁ B₂ C D} {h : C ⇒ D} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
             -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> (h ∘ g₁) ∘ f₁ ≈ (h ∘ g₂) ∘ f₂
  ∘²-resp-≈ˡ = unreassoc² ∘′ ∘-resp-≈ˡ

  ∘ˡ-resp-≈ʳ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : D ⇒ A}
             -> g ∘ f ≈ i -> g ∘ f ∘ h ≈ i ∘ h
  ∘ˡ-resp-≈ʳ = reassocˡ ∘′ ∘-resp-≈ʳ

  ∘ʳ-resp-≈ʳ : ∀ {A B C D} {g : B ⇒ C} {f : A ⇒ B} {i : A ⇒ C} {h : D ⇒ A}
             -> i ≈ g ∘ f -> i ∘ h ≈ g ∘ f ∘ h
  ∘ʳ-resp-≈ʳ = reassocʳ ∘′ ∘-resp-≈ʳ

  ∘²-resp-≈ʳ : ∀ {A B₁ B₂ C D} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {h : D ⇒ A}
             -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> g₁ ∘ f₁ ∘ h ≈ g₂ ∘ f₂ ∘ h
  ∘²-resp-≈ʳ = reassoc² ∘′ ∘-resp-≈ʳ

  _⌈_⌉ˡ_ : ∀ {A B₁ B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {g₁ g₁' : B₁ ⇒ C} {g₂ g₂' : B₂ ⇒ C}
         -> g₁ ≈ g₁' -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> g₂ ≈ g₂' -> g₁' ∘ f₁ ≈ g₂' ∘ f₂
  p ⌈ r ⌉ˡ q = ∘-resp-≈ʳ p ⌈ r ⌉ ∘-resp-≈ʳ q

  _ʳ⌈_⌉ˡ_ : ∀ {A B₁ B₁₁ B₂₁ B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
              {g₁₁ : B₁ ⇒ B₁₁} {g₁₂ : B₁₁ ⇒ C} {g₂₁ : B₂ ⇒ B₂₁} {g₂₂ : B₂₁ ⇒ C}
          -> g₁ ≈ g₁₂ ∘ g₁₁
          -> g₁ ∘ f₁ ≈ g₂ ∘ f₂
          -> g₂ ≈ g₂₂ ∘ g₂₁
          -> g₁₂ ∘ g₁₁ ∘ f₁ ≈ g₂₂ ∘ g₂₁ ∘ f₂
  p ʳ⌈ r ⌉ˡ q = ∘ʳ-resp-≈ʳ p ⌈ r ⌉ ∘ʳ-resp-≈ʳ q

  _²⌈_⌉ˡ_ : ∀ {A B₁ B₁₁ B₁₁' B₂₁ B₂₁' B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂}
              {g₁₁ : B₁ ⇒ B₁₁} {g₁₁' : B₁ ⇒ B₁₁'} {g₁₂ : B₁₁ ⇒ C} {g₁₂' : B₁₁' ⇒ C}
              {g₂₁ : B₂ ⇒ B₂₁} {g₂₁' : B₂ ⇒ B₂₁'} {g₂₂ : B₂₁ ⇒ C} {g₂₂' : B₂₁' ⇒ C}
          -> g₁₂ ∘ g₁₁ ≈ g₁₂' ∘ g₁₁'
          -> g₁₂ ∘ g₁₁ ∘ f₁ ≈ g₂₂ ∘ g₂₁ ∘ f₂
          -> g₂₂ ∘ g₂₁ ≈ g₂₂' ∘ g₂₁'
          -> g₁₂' ∘ g₁₁' ∘ f₁ ≈ g₂₂' ∘ g₂₁' ∘ f₂
  p ²⌈ r ⌉ˡ q = ∘²-resp-≈ʳ p ⌈ r ⌉ ∘²-resp-≈ʳ q

  _⌈_⌉ʳ_ : ∀ {A B₁ B₂ C} {f₁ f₁' : A ⇒ B₁} {f₂ f₂' : A ⇒ B₂} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
         -> f₁ ≈ f₁' -> g₁ ∘ f₁ ≈ g₂ ∘ f₂ -> f₂ ≈ f₂' -> g₁ ∘ f₁' ≈ g₂ ∘ f₂'
  p ⌈ r ⌉ʳ q = ∘-resp-≈ˡ p ⌈ r ⌉ ∘-resp-≈ˡ q

  _ʳ⌈_⌉ʳ_ : ∀ {A A₁₁ A₂₁ B₁ B₂ C} {f₁ : A ⇒ B₁} {f₂ : A ⇒ B₂} {g₁ : B₁ ⇒ C} {g₂ : B₂ ⇒ C}
             {f₁₁ : A ⇒ A₁₁} {f₁₂ : A₁₁ ⇒ B₁} {f₂₁ : A ⇒ A₂₁} {f₂₂ : A₂₁ ⇒ B₂}
         -> f₁ ≈ f₁₂ ∘ f₁₁
         -> g₁ ∘ f₁ ≈ g₂ ∘ f₂
         -> f₂ ≈ f₂₂ ∘ f₂₁
         -> (g₁ ∘ f₁₂) ∘ f₁₁ ≈ (g₂ ∘ f₂₂) ∘ f₂₁
  p ʳ⌈ r ⌉ʳ q = ∘ʳ-resp-≈ˡ p ⌈ r ⌉ ∘ʳ-resp-≈ˡ q
