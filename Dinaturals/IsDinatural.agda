{-# OPTIONS --safe --without-K #-}

{-
Various predicates to state whether two dinaturals compose/all dinaturals compose.
-}
module Dinaturals.IsDinatural where

open import Categories.Category.Lift

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
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Hom using (Hom[_][-,-]; Hom[_][_,-])
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.Equivalence renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper; NaturalIsomorphism)
open import Categories.Object.Terminal using (Terminal)
open import Data.List using ([]; _∷_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax; _×_; Σ; map-Σ)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Groupoid using (IsGroupoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Relation.Binary.Setoid.Equality using () renaming (_≈_ to _≈ᵖ_; setoid to FunctionSetoid)
open import Relation.Binary.Construct.Always using () renaming (setoid to alwaysSetoid)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

open Category using (op)

-- Predicate that states whether a family of morphisms α : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ] is dinatural.
IsDinaturalFamily : {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F G : Bifunctor (Category.op C) C D)
  (let module F = Functor F)
  (let module G = Functor G)
  → (α : ∀ X → D [ F.F₀ (X , X) , G.F₀ (X , X) ]) → Set (o ⊔ ℓ ⊔ e′)
IsDinaturalFamily {C = C} {D = D} F G α =
  ∀ {X Y} (f : C [ X , Y ]) →
                [ F.F₀ (Y , X) ⇒ G.F₀ (X , Y) ]⟨
                  F.F₁ (f , C.id)             ⇒⟨ F.F₀ (X , X) ⟩
                  α X                         ⇒⟨ G.F₀ (X , X) ⟩
                  G.F₁ (C.id , f)
                ≈ F.F₁ (C.id , f)             ⇒⟨ F.F₀ (Y , Y) ⟩
                  α Y                         ⇒⟨ G.F₀ (Y , Y) ⟩
                  G.F₁ (f , C.id)
                ⟩ where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G

  open D hiding (op)
  open Commutation D

-- Predicate that states whether two dinaturals compose.
CompositionIsDinatural : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} →
  ∀ {F G H : Functor (Product (op C) C) D}
  → (α : DinaturalTransformation F G)
  → (β : DinaturalTransformation G H)
  → Set (o ⊔ ℓ ⊔ e′)
CompositionIsDinatural {D = D} {F = F} {H = H} α β =
  let open Category D
      module α = DinaturalTransformation α
      module β = DinaturalTransformation β in
    IsDinaturalFamily F H (λ X → β.α X ∘ α.α X)

-- Predicate that states that all dinaturals for functors [Cop x C, D] compose.
AllDinaturalsCompose : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
AllDinaturalsCompose C D =
  ∀ {F G H : Functor (Product (op C) C) D}
  → (α : DinaturalTransformation F G)
  → (β : DinaturalTransformation G H)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → CompositionIsDinatural α β
