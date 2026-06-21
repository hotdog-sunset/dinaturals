{-# OPTIONS --safe --without-K #-}

{-
The finite category with two objects 0, 1 and one morphism 0 → 1.
-}

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

open import Categories.Category.Finite.Fin
open import Categories.Category.Core

private
  variable
    a b c d : Fin 2

IntervalShape : FinCatShape
IntervalShape = shapeHelper record
  { size      = 2
  ; ∣_⇒_∣     = card
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where card : Fin 2 → Fin 2 → ℕ
        card 0F 0F = 1
        card 0F 1F = 1
        card 1F 0F = 0
        card 1F 1F = 1

        id : Fin (card a a)
        id {0F} = 0F
        id {1F} = 0F

        _∘_ : ∀ {a b c} → Fin (card b c) → Fin (card a b) → Fin (card a c)
        _∘_ {0F} {0F} {0F} 0F 0F = 0F
        _∘_ {0F} {0F} {1F} 0F 0F = 0F
        _∘_ {0F} {1F} {1F} 0F 0F = 0F
        _∘_ {1F} {1F} {1F} 0F 0F = 0F

        assoc : ∀ {f : Fin (card a b)} {g : Fin (card b c)} {h : Fin (card c d)} →
                  ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
        assoc {0F} {0F} {0F} {0F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {1F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {1F} {1F} {1F} {1F} {0F} {0F} {0F} = refl

        identityˡ : ∀ {a b} {f : Fin (card a b)} → (id ∘ f) ≡ f
        identityˡ {0F} {0F} {0F} = refl
        identityˡ {0F} {1F} {0F} = refl
        identityˡ {1F} {1F} {0F} = refl

        identityʳ : ∀ {a b} {f : Fin (card a b)} → (f ∘ id) ≡ f
        identityʳ {0F} {0F} {0F} = refl
        identityʳ {0F} {1F} {0F} = refl
        identityʳ {1F} {1F} {0F} = refl

Interval : Category _ _ _
Interval = FinCategory IntervalShape

module Interval = Category Interval
