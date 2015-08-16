module Categories.Yoneda.Simple where

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom
open import Categories.NaturalTransformation
open import Categories.Categories.Agda

liftStructSetoid : ∀ {α β} α' β'
                 -> [ Setoid S β ∣ S ∈ Set α ] -> [ Setoid S (β ⊔ β') ∣ S ∈ Set (α ⊔ α') ]
liftStructSetoid α' β' (hide setoid) = hide record
  { _≈_           = λ x y -> Lift {ℓ = β'} (lower {ℓ = α'} x ≈ lower y)
  ; isEquivalence = record
      { refl  = lift refl
      ; sym   = lift ∘′ sym ∘′ lower
      ; trans = λ p q -> lift (trans (lower p) (lower q))
      }
  } where open Setoid setoid

module _ {α β γ} {C : Category α β γ} (F : Copresheaf {β} {γ} C) where
  open Category C hiding (inst); open Functor F
  module _ {α' γ'} where
    Setoids' = Setoids {α'} {γ'}

    open Category₂ Setoids' hiding (inst) public
    open import Categories.Morphism Setoids' public
    open ISetoid (NaturalTransformation-ISetoid {C₁ = C} {Setoids'}) using (inst) public

  module _ A where
    nat : [ Setoid S _ ∣ S ∈ Set _ ]
    nat = record
      { hiden  = NaturalTransformation Hom[ A ,-] F
      ; reveal = inst _
      }

    set : [ Setoid S _ ∣ S ∈ Set _ ]
    set = liftStructSetoid (α ⊔ suc (β ⊔ γ)) (α ⊔ β) (F· A)

    postulate ⊥ : ∀ {α} {A : Set α} -> A

    Yoneda : nat ≃ set
    Yoneda = record
      { f   = f
      ; f⁻¹ = f⁻¹
      ; iso = record
            -- It's a trivial proposition, but Agda eats 1 GB RAM
            -- and doesn't allow to finish the proof on my machine. 
          { isoˡ = ⊥
          ; isoʳ = isoʳ
          }
      } where
          open Setoid₁ (reveal (F· A))

          f : nat ⇒₂ set
          f = record
            { f·       = λ N -> let open NaturalTransformation N in lift (η ⟨$⟩ id)
            ; f-resp-≈ = λ p -> lift (p refl)
            }

          f⁻¹ : set ⇒₂ nat
          f⁻¹ = record
            { f·       = λ{ (lift x) -> record
                  { η          = λ {B} -> record
                      { f·       = λ f -> F⇒ f ⟨$⟩ x
                      ; f-resp-≈ = λ p -> F-resp-≈ p refl₁
                      }
                  ; naturality = λ {B C g f₁ f₂} p ->
                      let open Π (F⇒ g)
                          open EqReasoning₁ (reveal (F· C))
                          open EqReasoning₂ (reveal (F· B)) in
                        begin₁
                          F⇒ (g ∘ f₁ ∘ id) ⟨$⟩ x      →⟨ F-∘ refl₁ ⟩₁
                          F⇒ g ⟨$⟩ F⇒ (f₁ ∘ id) ⟨$⟩ x →⟨ f-resp-≈ $
                              begin₂
                                F⇒ (f₁ ∘ id) ⟨$⟩ x →⟨ F-resp-≈ idʳ refl₁ ⟩₂
                                F⇒ f₁ ⟨$⟩ x        →⟨ F-resp-≈ p   refl₁ ⟩₂
                                F⇒ f₂ ⟨$⟩ x
                              ∎₂
                            ⟩₁
                          F⇒ g ⟨$⟩ (F⇒ f₂ ⟨$⟩ x)
                        ∎₁         
                  }
                }
            ; f-resp-≈ = λ p q -> F-resp-≈ q (lower p)
            }

          isoʳ : f ∘₂ f⁻¹ ≈₂ id₂
          isoʳ = lift ∘′ F-id ∘′ lower
