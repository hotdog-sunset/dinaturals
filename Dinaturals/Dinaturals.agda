{-# OPTIONS --safe --without-K --lossy-unification #-}

{-
Various constructions about (Set-valued) dinaturals, used in other files.
-}
module Dinaturals.Dinaturals where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)
open import Categories.Category.Instance.Properties.Setoids using (Setoids-CCC; Setoids-Cocomplete)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using (Product; πˡ; πʳ; _⁂_; _※_; assocˡ; assocʳ; Swap)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₁; [_]-decompose₂; [_]-merge; [_]-commute)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper) renaming (_≃_ to _≃ᵈ_)
open import Data.Product using (_,_; proj₁; proj₂) renaming (_×_ to _×′_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Construct.Identity renaming (function to idS)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

private
  variable
    o ℓ e : Level
    Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

infixr 5 _⊗_
infixr 5 _$_

private
  _⊗_ = Product
  _$_ = _⟨$⟩_

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

-- The identity dinatural transformation for a functor A : (C^op x C) -> Set, given by the identity function in each component.
id-din : {A : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
        → DinaturalTransformation A A
id-din {A = A} = let module A = Functor A in dtHelper record
  { α = λ X → idS (A.₀ (X , X))
  ; commute = λ f → [ A ]-commute
  }

-- The eval map for a functor A : (C^op x C) -> Set, given by the evaluation map of the cartesian closed structure on presheaves.
-- Note that this dinatural does not compose on the left with other dinaturals, and hence it is not strong.
eval-din : {A B : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
          → DinaturalTransformation (SetA.-×- ∘F (A ※ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))) B
eval-din {A = A} {B = B} = dtHelper
  record
    { α = λ X → record
      { to = λ { (v , f) → f ⟨$⟩ v }
      ; cong = λ { {r , o} {p , q} (v , f) → Setoid.trans (B.F₀ (X , X)) f (Func.cong q v) }
      }
    ; commute = λ { {X} {Y} f {v , h} →
    let open Setoid (B.₀ (X , Y)) in
      trans [ B ]-commute (Func.cong (B.₁ _) (Func.cong (B.₁ _) (Func.cong h [ A ]-commute)))
    } } where
    module A = Functor A
    module B = Functor B

-- Product of dinaturals.
productd : {A B Φ : Functor (op Γ ⊗ Γ) (Setoids ℓ ℓ)}
          → DinaturalTransformation Φ A
          → DinaturalTransformation Φ B
          → DinaturalTransformation Φ (SetA.-×- ∘F (A ※ B))
productd α β = dtHelper record
  { α = λ X → < α.α X , β.α X >ₛ
  ; commute = λ _ → α.commute _ , β.commute _
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β

-- Implication is functorial for dinaturals.
⇨-functor-dinat : ∀ {ℓ} {C : Category ℓ ℓ ℓ} {A B A′ B′ : Functor (Product (op C) C) (Setoids ℓ ℓ)}
  → DinaturalTransformation A′ A
  → DinaturalTransformation B B′
  → DinaturalTransformation (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B))
                            (Set.-⇨- ∘F (Functor.op A′ ∘F Swap ※ B′))
⇨-functor-dinat {C = C} {A = A} {B = B} {A′ = A′} {B′ = B′} α β = dtHelper record
  { α = λ X → record
    { to = λ f → record
      { to = λ v → β.α X $ f $ α.α X $ v
      ; cong = λ x → Func.cong (β.α X) (Func.cong f (Func.cong (α.α X) x))
      }
    ; cong = λ fe → Func.cong (β.α X) fe
    }
  ; commute = λ { {X} {Y} f {h} {v} →
      let open RS (B′.F₀ (X , Y)) in
        begin B′.₁ (C.id , f) $ β.α X $ B.₁ (f , C.id) $ h $ A.₁ (C.id , f) $ α.α X $ A′.₁ (f , C.id) $ v ≈⟨ β.commute f ⟩
              B′.₁ (f , C.id) $ β.α Y $ B.₁ (C.id , f) $ h $ A.₁ (C.id , f) $ α.α X $ A′.₁ (f , C.id) $ v ≈⟨ Func.cong (B′.F₁ (f , C.id)) (Func.cong (β.α Y) (Func.cong (B.₁ (C.id , f)) (Func.cong h (α.commute f)))) ⟩
              B′.F₁ (f , C.id) $ β.α Y $ B.₁ (C.id , f) $ h $ A.₁ (f , C.id) $ α.α Y $ A′.₁ (C.id , f) $ v ∎
    }
  } where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module C = Reason C
    module A = Functor A
    module B = Functor B
    module A′ = Functor A′
    module B′ = Functor B′
    module AS {X} {Y} = RS (A.₀ (X , Y))
    module BS {X} {Y} = RS (B.₀ (X , Y))
    module A′S {X} {Y} = RS (A′.₀ (X , Y))
    module B′S {X} {Y} = RS (B′.₀ (X , Y))
