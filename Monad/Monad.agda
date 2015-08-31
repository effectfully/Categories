module Categories.Monad.Monad where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

record Monad {α β γ} (C : Category α β γ) : Set (α ⊔ β ⊔ γ) where
  field
    T : Endofunctor C
    η : NaturalTransformation idᶠ T
    μ : NaturalTransformation (T ∘ᶠ T) T

  open Category C
  open NaturalTransformation η using (naturality)

  -- Can't resist.
  open Functor T renaming (F· to ⟨_⟩; F⇒ to fmap;
                           F-∘ to fmap-∘; F-id to fmap-id; F-resp-≈ to fmap-resp-≈) public
  open NaturalTransformation η renaming (η to pure) hiding (naturality)             public
  open NaturalTransformation μ renaming (η to join; naturality to join-fmap-fmap)   public

  field
    join-pure      : ∀ {A} -> join {A} ∘ pure      ≈ id
    join-fmap-pure : ∀ {A} -> join {A} ∘ fmap pure ≈ id
    join-fmap-join : ∀ {A} -> join {A} ∘ fmap join ≈ join ∘ join

  fmap-pure : ∀ {A B} {f : A ⇒ B} -> fmap f ∘ pure ≈ pure ∘ f
  fmap-pure = sym naturality

  _>=>_ : ∀ {A B C} -> A ⇒ ⟨ B ⟩ -> B ⇒ ⟨ C ⟩ -> A ⇒ ⟨ C ⟩
  f >=> g = join ∘ fmap g ∘ f

  -- open Hetero (setoidⁿ {C₁ = C} {C₂ = C})
  -- idˡₘ   : μₘ ∘ⁿ (Fₘ ∘ˡ ηₘ) ≋ idⁿ {F = Fₘ}
  -- idʳₘ   : μₘ ∘ⁿ (ηₘ ∘ʳ Fₘ) ≋ idⁿ {F = Fₘ}
  -- assocₘ : μₘ ∘ⁿ (Fₘ ∘ˡ μₘ) ≋ μₘ ∘ⁿ (μₘ ∘ʳ Fₘ)
