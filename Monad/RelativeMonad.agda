module Categories.Monad.RelativeMonad where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

-- class (Functor j, Functor t) => RelativeMonad j t where
--   return :: j a -> t a
--   (>>=)  :: t a -> (j a -> t b) -> t b

record RelativeMonad {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
                     (J : Functor C₁ C₂) : Set (α₁ ⊔ α₂ ⊔ β₁ ⊔ β₂ ⊔ γ₁ ⊔ γ₂) where
  field
    T : Functor C₁ C₂
    η : NaturalTransformation J T
    
  open Category₁ C₁; open Category C₂
  open NaturalTransformation η using (naturality)

  open Functor J renaming (F· to ⟨_⟩₀; F⇒ to fmap₀;
                           F-∘ to fmap-∘₀; F-id to fmap-id₀; F-resp-≈ to fmap-resp-≈₀) public
  open Functor T renaming (F· to ⟨_⟩ ; F⇒ to fmap ;
                           F-∘ to fmap-∘ ; F-id to fmap-id ; F-resp-≈ to fmap-resp-≈ ) public
  open NaturalTransformation η renaming (η to pure) hiding (naturality)                public

  -- I can't call it `bind'. It's kinda a natural transformation component,
  -- but ⟨ A ⟩₀ and ⟨ A ⟩ are related through ⟨ B ⟩, so I call it "relative eta".
  field
    releta : ∀ {A B} -> ⟨ A ⟩₀ ⇒ ⟨ B ⟩ -> ⟨ A ⟩ ⇒ ⟨ B ⟩

    releta-pure     : ∀ {A B} {f : ⟨ A ⟩  ⇒ ⟨ B ⟩} -> releta (f ∘ pure) ≈ f
    releta-∘-pure   : ∀ {A B} {f : ⟨ A ⟩₀ ⇒ ⟨ B ⟩} -> releta  f ∘ pure  ≈ f
    releta-releta-∘ : ∀ {A B} {f : ⟨ A ⟩₀ ⇒ ⟨ B ⟩} {g : ⟨ B ⟩₀ ⇒ ⟨ A ⟩}
                    -> releta (releta g ∘ f) ≈ releta g ∘ releta f
    releta-resp-≈   : ∀ {A B} {f g : ⟨ A ⟩₀ ⇒ ⟨ B ⟩} -> f ≈ g -> releta f ≈ releta g

  fmap-pure : ∀ {A B} {f : A ⇒₁ B} -> fmap f ∘ pure ≈ pure ∘ fmap₀ f
  fmap-pure = sym naturality

  -- It could be `A' instead of ⟨ A ⟩₀.
  _<=<_ : ∀ {A B C} -> ⟨ B ⟩₀ ⇒ ⟨ C ⟩ -> ⟨ A ⟩₀ ⇒ ⟨ B ⟩ -> ⟨ A ⟩₀ ⇒ ⟨ C ⟩
  g <=< f = releta g ∘ f

  _>=>_ : ∀ {A B C} -> ⟨ A ⟩₀ ⇒ ⟨ B ⟩ -> ⟨ B ⟩₀ ⇒ ⟨ C ⟩ -> ⟨ A ⟩₀ ⇒ ⟨ C ⟩
  _>=>_ = flip _<=<_
