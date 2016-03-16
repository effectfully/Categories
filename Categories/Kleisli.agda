open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Monad.Core

module Categories.Categories.Kleisli {α β γ} {C : Category α β γ} (M : Monad C) where

open IEqReasoningWith C; open Monad M

Kleisli : Category α β γ
Kleisli = record
  { Obj      = Obj
  ; _⇒_      = λ A B -> A ⇒ ⟨ B ⟩
  ; setoid   = coerceⁱˢ setoid
  ; id       = pure
  ; _∘_      = _<=<_
  ; idˡ      = λ {_ _ f} ->
      begin
        join ∘ fmap pure ∘ f →⟨ ∘ˡ-resp-≈ʳ join-fmap-pure ⟩
        id ∘ f               →⟨ idˡ                       ⟩
        f
      ∎
  ; idʳ      = λ {_ _ f} ->
      begin
        join ∘ fmap f ∘ pure →⟨ ∘ʳ-resp-≈ˡ fmap-pure ⟩
        (join ∘ pure) ∘ f    →⟨ ∘-resp-≈ʳ join-pure  ⟩
        id ∘ f               →⟨ idˡ                  ⟩
        f
      ∎
  ; assoc    = λ {_ _ _ _ h g f} ->
      begin
        join ∘ fmap (join ∘ fmap h ∘ g) ∘ f   →⟨ ∘ˡ-resp-≈ʳ      $
          begin
            join ∘ fmap (join ∘ fmap h ∘ g)        →⟨ ∘-resp-≈ˡ fmap-∘                       ⟩
            join ∘ fmap join ∘ fmap (fmap h ∘ g)   →⟨ ∘ˡ-resp-≈ʳ join-fmap-join              ⟩
            (join ∘ join) ∘ fmap (fmap h ∘ g)      →⟨ ∘-resp-≈ˡ fmap-∘                       ⟩
            (join ∘ join) ∘ fmap (fmap h) ∘ fmap g →⟨ ∘ˡ-resp-≈ʳ (∘ˡ-resp-≈ˡ join-fmap-fmap) ⟩
            (join ∘ fmap h ∘ join) ∘ fmap g
          ∎                                                       ⟩
        ((join ∘ fmap h ∘ join) ∘ fmap g) ∘ f →⟨ assoc            ⟩
        (join ∘ fmap h ∘ join) ∘ fmap g ∘ f   →⟨ ∘ˡ-resp-≈ˡ assoc ⟩
        join ∘ fmap h ∘ join ∘ fmap g ∘ f
      ∎
  ; ∘-resp-≈ = λ q p -> ∘-resp-≈ˡ (∘-resp-≈ (fmap-resp-≈ q) p)
  }
