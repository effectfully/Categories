# Categories

## In short

Here I study some basic category theory.

## [Setoids](https://github.com/effectfully/Categories/blob/master/Setoid/Setoid.agda)

There are three kinds of setoids in this development:

 - usual setoids                   (underlying equality is `_≈_ :            A   -> A   -> Set β`)
 - indexed setoids                 (underlying equality is `_≈_ : ∀ {i}   -> A i -> A i -> Set β`)
 - heterogeneously indexed setoids (underlying equality is `_≈_ : ∀ {i j} -> A i -> A j -> Set β`)

All of them are used in the code.

There is a [module](https://github.com/effectfully/Categories/blob/master/Setoid/Setoid.agda#L131) that performs transformation of an indexed setoid into its henerogeneously indexed counterpart. This is used in the [definition](https://github.com/effectfully/Categories/blob/master/Functor/Functor.agda#L130) of a `Functor` setoid. One especially nice thing about this transformation is that we [can](https://github.com/effectfully/Categories/blob/master/Setoid/Instances.agda#L57) define Agda's heterogeneous equality in terms of propositional equality. It's just

    module Just-HEquality {α} = Hetero (≡-ISetoid {α = α} {A = id′}) renaming (_≋_ to _≅_)

I.e. turn indices into sets and your indexed propositional equality is plain heterogeneous equality now. A [test](https://github.com/effectfully/Categories/blob/master/Setoid/Instances.agda#L83).

There are several functions that allow to define setoids from other setoids ([one family](https://github.com/effectfully/Categories/blob/master/Setoid/Setoid.agda#L69) and [another](https://github.com/effectfully/Categories/blob/master/Setoid/Setoid.agda#L206)). Most setoids in the development are defined with the help from these functions. E.g. a natural transformations setoid

    setoidⁿ : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂} {C₁ : Category α₁ β₁ γ₁} {C₂ : Category α₂ β₂ γ₂}
            -> ISetoid₂ (NaturalTransformation {C₁ = C₁} {C₂ = C₂}) (α₁ ⊔ γ₂)
    setoidⁿ {C₂ = C₂} = comap∀ⁱˢ (λ N A -> let open NaturalTransformation N in η {A}) setoid
      where open Category C₂

is defined in terms of a target category setoid. One another example is a setoid for the [Comma](https://github.com/effectfully/Categories/blob/master/Categories/Comma.agda#L16) category:

    setoid = comapⁱˢ₁ (λ{ (f₁ , f₂ , _) -> f₁ , f₂ }) (setoid₁ ×ⁱˢ setoid₂)

This says "use morphisms equalities from the corresponding categories and ignore commutativity proofs".

## Some results

Categories stuff is pretty standard and much like in [this](https://github.com/copumpkin/categories) development, on which I consult all the time.

 - [Four variants of the `Agda` category with a few simple properties like "**Set** has pullbacks"](https://github.com/effectfully/Categories/blob/master/Categories/Agda.agda).
 - [A variant of the Yoneda lemma, stated using Agda's quantification instead of the Yoneda embedding](https://github.com/effectfully/Categories/blob/master/Yoneda/Simple.agda).
 - [The pullback pasting lemma](https://github.com/effectfully/Categories/blob/master/Object/Limit/Properties/Pullback.agda) (for some reason the code typechecks only after copying it into Pullback.agda).
 - [Products are limits](https://github.com/effectfully/Categories/blob/master/Object/Limit/Properties/Product.agda).
 - [Lambda terms form a natural transformation](https://github.com/effectfully/Categories/blob/master/NaturalTransformation/Lambda.agda).
 - [Two failed attempts to construct coequalizers in **FinSet**](https://github.com/effectfully/Categories/tree/master/Examples/Eqclasses) (I'm not giving up).