{-# OPTIONS --safe --without-K #-}

{-
We prove that if for every family P : A → Set there is a bijection between terms

  (x : A) → x ≡ x → P x

and

  (x : A) → P x

then A is a set.
We consider here only the case where P depends on x and is not mute.
-}
module Dinaturals.BijectionRefl where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Data.Unit
open import Function.Base
open import Function.Related.Propositional
open import Axiom.UniquenessOfIdentityProofs
open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong-app)
open import Relation.Binary.Definitions

private
  variable
    ℓ : Level

record IsBijection (A B : Set ℓ) (to : A → B) (from : B → A) : Set (sucℓ ℓ) where
  field
    to-from : ∀ b → to (from b) ≡ b
    from-to : ∀ a → from (to a) ≡ a

-- The type of entailments for P with an extra reflexive equality in the domain.
EntailmentRefl : (A : Set ℓ) → (P : A → Set (sucℓ ℓ)) → Set (sucℓ ℓ)
EntailmentRefl A P = (x : A) → x ≡ x → P x

-- The type of entailments for P in the empty context.
EntailmentGeneric : (A : Set ℓ) → (P : A → Set (sucℓ ℓ)) → Set (sucℓ ℓ)
EntailmentGeneric A P = (x : A) → P x

-- The two directions of the bijection: compose with refl, and ignore the equality.
compose-with-refl : ∀ {A : Set ℓ} {P : A → Set (sucℓ ℓ)} → EntailmentRefl A P → EntailmentGeneric A P
compose-with-refl f = λ a → f a refl

forget-eq : ∀ {A : Set ℓ} {P : A → Set (sucℓ ℓ)} → EntailmentGeneric A P → EntailmentRefl A P
forget-eq f = λ a e → f a

-- Direction 1: if A is a set, then it is a bijection.
uip⇒bijection : ∀ {A : Set ℓ}
    → (funext : ∀ {ℓ} → Extensionality ℓ (sucℓ ℓ))
    → Irrelevant {A = A} _≡_
    → (∀ (P : A → Set (sucℓ ℓ))
      → IsBijection (EntailmentGeneric A P)
                    (EntailmentRefl A P)
                    (forget-eq {A = A})
                    (compose-with-refl {A = A}))
uip⇒bijection funext irrelevant P = record
  { to-from = λ b → funext λ x → funext λ y → cong (b x) (irrelevant refl y)
  ; from-to = λ a → funext λ x → refl
  }

lift-injective
  : ∀ {A : Set ℓ} {ℓ′ : Level} {x y : A}
  → lift {ℓ = ℓ′} x ≡ lift {ℓ = ℓ′} y
  → x ≡ y
lift-injective {A} {x} {y} refl = refl

-- Direction 2: if there is a bijection for every P then A is a set. The idea is to take P as the family of reflexive equalities.ì
bijection⇒uip : ∀ {A : Set ℓ}
    → (funext : ∀ {ℓ} → Extensionality ℓ (sucℓ ℓ))
    → (∀ (P : A → Set (sucℓ ℓ))
      → IsBijection (EntailmentGeneric A P)
                    (EntailmentRefl A P)
                    (forget-eq {A = A})
                    (compose-with-refl {A = A}))
    → Irrelevant {A = A} _≡_
bijection⇒uip {ℓ} funext dd = λ { refl →
  let m = (bijection.to-from λ x → Lift (sucℓ ℓ) (x ≡ x)) λ p q → lift q
   in λ e → lift-injective (cong-app (cong-app m _) e) }
  where
    module bijection P = IsBijection (dd P)
