{-# OPTIONS --safe --without-K #-}

module Dinaturals.LoopCompositionWithRefl where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid; SingletonSetoid-⊤)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic using (⊤)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.Always using () renaming (setoid to alwaysSetoid)

open Functor using (F₀; F₁; homomorphism)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturals.LoopComposition

private
  variable
    o ℓ e : Level
    A B C Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module P-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

-- The terminal setoid, which we redefine because agda-stdlib setoids are not level polymorphic in both object and equality levels.
UnitSetoid : Setoid ℓ ℓ
UnitSetoid = alwaysSetoid ⊤ _

-- The refl dinatural transformation.
refl : ∀ {o} (A : Category o ℓ ℓ)
     → DinaturalTransformation
          (const {D = Setoids ℓ ℓ} {C = Product (Category.op A) A} UnitSetoid)
          (Hom[ A ][-,-])
refl A =
  let open Reason A in
    dtHelper record
    { α = λ X → record
      { to = λ x → id
      ; cong = λ x → Equiv.refl
      }
    ; commute = λ f → id-swap-2
    }

-- The three different kinds of loop-composition with the refl dinatural transformation,
-- all of which use P mute (i.e., P is just a setoid).
loopComposeMuteWithRefl⁻ : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (P : Setoid ℓ ℓ)
      → DinaturalTransformation Hom[ A ][-,-] (const P)
      → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ const UnitSetoid)) (const P)
loopComposeMuteWithRefl⁻ {A = A} P α = compositionUpToLoop⁻ (refl A) α

loopComposeMuteWithRefl⁺ : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (P : Setoid ℓ ℓ)
      → DinaturalTransformation Hom[ A ][-,-] (const P)
      → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ const UnitSetoid)) (const P)
loopComposeMuteWithRefl⁺ {A = A} P α = compositionUpToLoop⁺ (refl A) α

loopComposeMuteWithRefl⁻⁺ : ∀ {o ℓ} {A : Category o ℓ ℓ}
      → (P : Setoid ℓ ℓ)
      → DinaturalTransformation Hom[ A ][-,-] (const P)
      → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ const UnitSetoid)) (const P)
loopComposeMuteWithRefl⁻⁺ {A = A} P α = compositionUpToLoop⁻⁺ (refl A) α

------------------------------------------------------

-- Dinaturality conditions for the three kinds of composition.

module comp⁺ {o} {ℓ} {A : Category o ℓ ℓ} P α = DinaturalTransformation (loopComposeMuteWithRefl⁻ {A = A} P α)
module comp⁻ {o} {ℓ} {A : Category o ℓ ℓ} P α = DinaturalTransformation (loopComposeMuteWithRefl⁺ {A = A} P α)
module comp⁻⁺ {o} {ℓ} {A : Category o ℓ ℓ} P α = DinaturalTransformation (loopComposeMuteWithRefl⁻⁺ {A = A} P α)

-- Contravariant and covariant compositions match with the original dinatural.

loopComposeMuteWithRefl⁺-condition : ∀ {o ℓ} {A : Category o ℓ ℓ}
  → (P : Setoid ℓ ℓ)
  → (α : DinaturalTransformation Hom[ A ][-,-] (const P))
  → (let module α = DinaturalTransformation α)
  → (let open Reason A)
  → {X Y : Category.Obj A} (f : X ⇒ Y) (g : Y ⇒ X) →
      (Setoid._≈_ P
       (α.α X $ (id ∘ id ∘ id ∘ g ∘ f))
       (α.α Y $ (id ∘ id ∘ f ∘ g ∘ id)))
loopComposeMuteWithRefl⁺-condition {A = A} P α f g =
  let open Reason A in comp⁺.commute P α f {x = g , _}

loopComposeMuteWithRefl⁻-condition : ∀ {o ℓ} {A : Category o ℓ ℓ}
  → (P : Setoid ℓ ℓ)
  → (α : DinaturalTransformation Hom[ A ][-,-] (const P))
  → (let module α = DinaturalTransformation α)
  → (let open Reason A)
  → {X Y : Category.Obj A} (f : X ⇒ Y) (g : Y ⇒ X) →
      (Setoid._≈_ P
        (α.α X $ ((id ∘ g ∘ f) ∘ id ∘ id))
        (α.α Y $ ((f ∘ g ∘ id) ∘ id ∘ id)))
loopComposeMuteWithRefl⁻-condition {A = A} P α f g =
  let open Reason A in comp⁻.commute P α f {x = g , _}

-- Two-sided composition has a different dinaturality condition since it composes two times with the endomorphism.

loopComposeMuteWithRefl⁻⁺-condition : ∀ {o ℓ} {A : Category o ℓ ℓ}
  → (P : Setoid ℓ ℓ)
  → (α : DinaturalTransformation Hom[ A ][-,-] (const P))
  → (let module α = DinaturalTransformation α)
  → (let open Reason A)
  → {X Y : Category.Obj A} (f : X ⇒ Y) (g : Y ⇒ X) →
      (Setoid._≈_ P
        (α.α X $ ((id ∘ g ∘ f) ∘ id ∘ id ∘ g ∘ f))
        (α.α Y $ ((f ∘ g ∘ id) ∘ id ∘ f ∘ g ∘ id)))
loopComposeMuteWithRefl⁻⁺-condition {A = A} P α f g =
  let open Reason A in comp⁻⁺.commute P α f {x = g , _}

-- In this special case, the negative and positive loop compositions match.

loopComposeMuteWithRefl-⁻-⁺-match : ∀ {o ℓ} {A : Category o ℓ ℓ}
  → (P : Setoid ℓ ℓ)
  → (α : DinaturalTransformation Hom[ A ][-,-] (const P))
  → loopComposeMuteWithRefl⁻ {A = A} P α
  ≃ᵈ loopComposeMuteWithRefl⁺ {A = A} P α
loopComposeMuteWithRefl-⁻-⁺-match {A = A} P α =
  let open Reason A
      module α = DinaturalTransformation α in
    Func.cong (α.α _) sym-id-swap-2
