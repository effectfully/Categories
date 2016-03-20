open import Categories.Category

module Categories.Object {α β γ} (C : Category α β γ) where

open import Categories.Object.Limit.Terminal      C public
open import Categories.Object.Limit.Product       C public
open import Categories.Object.Limit.Equalizer     C public
open import Categories.Object.Limit.Pullback      C public
open import Categories.Object.Limit.Exponential   C public
open import Categories.Object.Limit.Relations     C public
open import Categories.Object.Colimit.Initial     C public
open import Categories.Object.Colimit.Coproduct   C public
open import Categories.Object.Colimit.Coequalizer C public
open import Categories.Object.Colimit.Pushout     C public
open import Categories.Object.Colimit.Relations   C public
