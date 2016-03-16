module Categories.Monad.Core where

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation

record Monad {α β γ} (C : Category α β γ) : Set (α ⊔ β ⊔ γ) where
  infixr 2 _<=<_ _>=>_

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

  -- Need irrelevance for this.
  -- Or heterogeneous equality: open Hetero (setoidⁿ {C₁ = C} {C₂ = C})
  -- But I have no idea how to use it then.
  -- field
  --   idˡₘ   : μ ∘ⁿ (T ∘ˡ η) ≈ⁿ idⁿ {F = T}
  --   idʳₘ   : μ ∘ⁿ (η ∘ʳ T) ≈ⁿ idⁿ {F = T}
  --   assocₘ : μ ∘ⁿ (T ∘ˡ μ) ≈ⁿ μ ∘ⁿ (μ ∘ʳ T)

  field
    join-pure      : ∀ {A} -> join {A} ∘ pure      ≈ id
    join-fmap-pure : ∀ {A} -> join {A} ∘ fmap pure ≈ id
    join-fmap-join : ∀ {A} -> join {A} ∘ fmap join ≈ join ∘ join

  fmap-pure : ∀ {A B} {f : A ⇒ B} -> fmap f ∘ pure ≈ pure ∘ f
  fmap-pure = sym naturality

  _<=<_ : ∀ {A B C} -> B ⇒ ⟨ C ⟩ -> A ⇒ ⟨ B ⟩ -> A ⇒ ⟨ C ⟩
  g <=< f = join ∘ fmap g ∘ f

  _>=>_ : ∀ {A B C} -> A ⇒ ⟨ B ⟩ -> B ⇒ ⟨ C ⟩ -> A ⇒ ⟨ C ⟩
  _>=>_ = flip _<=<_
