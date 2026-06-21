{-# OPTIONS --safe --without-K #-}

{-
The finite category with one object and two morphisms, the identity and another morphism f for which f ; f = f.
We use 0F for the identity and 1F for f.
-}

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

open import Categories.Category.Finite.Fin
open import Categories.Category.Core

private
  variable
    a b c d : Fin 1

NonTrivialEndoShape : FinCatShape
NonTrivialEndoShape = shapeHelper record
  { size      = 1
  ; ∣_⇒_∣     = card
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where card : Fin 1 → Fin 1 → ℕ
        card 0F 0F = 2

        id : Fin (card a a)
        id {0F} = 0F

        _∘_ : ∀ {a b c} → Fin (card b c) → Fin (card a b) → Fin (card a c)
        _∘_ {0F} {0F} {0F} 0F 0F = 0F
        _∘_ {0F} {0F} {0F} 0F 1F = 1F
        _∘_ {0F} {0F} {0F} 1F 0F = 1F
        _∘_ {0F} {0F} {0F} 1F 1F = 1F

        assoc : ∀ {f : Fin (card a b)} {g : Fin (card b c)} {h : Fin (card c d)} →
                  ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
        assoc {0F} {0F} {0F} {0F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {0F} {0F} {0F} {1F} = refl
        assoc {0F} {0F} {0F} {0F} {0F} {1F} {0F} = refl
        assoc {0F} {0F} {0F} {0F} {0F} {1F} {1F} = refl
        assoc {0F} {0F} {0F} {0F} {1F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {0F} {1F} {0F} {1F} = refl
        assoc {0F} {0F} {0F} {0F} {1F} {1F} {0F} = refl
        assoc {0F} {0F} {0F} {0F} {1F} {1F} {1F} = refl

        identityˡ : ∀ {a b} {f : Fin (card a b)} → (id ∘ f) ≡ f
        identityˡ {0F} {0F} {0F} = refl
        identityˡ {0F} {0F} {1F} = refl

        identityʳ : ∀ {a b} {f : Fin (card a b)} → (f ∘ id) ≡ f
        identityʳ {0F} {0F} {0F} = refl
        identityʳ {0F} {0F} {1F} = refl

NonTrivialEndo : Category _ _ _
NonTrivialEndo = FinCategory NonTrivialEndoShape

module NonTrivialEndo = Category NonTrivialEndo
