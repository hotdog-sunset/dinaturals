{-# OPTIONS --safe --without-K #-}

{-
This file contains the three loop-compositions in their co/contra/two-sided flavours.
-}
module Dinaturals.LoopComposition where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.Helper using (categoryHelper)
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
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

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
  variable
    F G I J L : Functor (op Γᵒᵖ ⊗ Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

pattern * = lift Data.Unit.tt

{-
Covariant, contravariant and two-sided compositions up-to loop all take the following shape:

F(x,x) -> G(x,x)      G(x,x) -> H(x,x)
--------------------------------------
   hom(x,x) x F(x,x) -> H(x,x)
-}

-- Covariant composition up-to loop.
compositionUpToLoop⁺ : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation F G
  → DinaturalTransformation G H
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ F)) H
compositionUpToLoop⁺ {A = A} {F = F} {G = G} {H = H} α β = dtHelper record
  { α = λ X → record
    { to = λ { (endo , p) → β.α X $ G.₁ (id , endo) $ α.α X $ p }
    ; cong = λ { (e , q) → Func.cong (β.α X) (GT.trans (Func.cong (G.₁ _) (Func.cong (α.α X) q)) (G.F-resp-≈ (refl , e))) }
    }
  ; commute = λ { {X} {Y} f {x , y} →
      let open RS (H.₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ G.₁ (id , id ∘ x ∘ f) $ α.α X $ F.₁ (f , id) $ y
              ≈˘⟨ Func.cong (H.₁ _) (Func.cong (β.α X) ([ G ]-merge id-0 sym-id-0)) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (id , x) $ G.₁ (id , f) $ α.α X $ F.₁ (f , id) $ y
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α X) (Func.cong (G.₁ _) (α.commute f))) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (id , x) $ G.₁ (f , id) $ α.α Y $ F.₁ (id , f) $ y
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α X) ([ G ]-resp-square (id-swap , id-swap))) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (f , id) $ G.₁ (id , x) $ α.α Y $ F.₁ (id , f) $ y
              ≈⟨ β.commute f ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (id , f) $ G.₁ (id , x) $ α.α Y $ F.₁ (id , f) $ y
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) ([ G ]-merge id-0 sym-id-2)) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (id , f ∘ x ∘ id) $ α.α Y $ F.₁ (id , f) $ y ∎
    }
  } where
    module A = Category A
    open Reason A
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module FS {X} {Y} = RS (F.₀ (X , Y))
    module GS {X} {Y} = RS (G.₀ (X , Y))
    module HS {X} {Y} = RS (H.₀ (X , Y))
    module FT {X} {Y} = Setoid (F.₀ (X , Y))
    module GT {X} {Y} = Setoid (G.₀ (X , Y))
    module HT {X} {Y} = Setoid (H.₀ (X , Y))

-- Contravariant composition up-to loop.
compositionUpToLoop⁻ : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation F G
  → DinaturalTransformation G H
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ F)) H
compositionUpToLoop⁻ {A = A} {F = F} {G = G} {H = H} α β = dtHelper record
  { α = λ X → record
    { to = λ { (endo , p) → β.α X $ G.₁ (endo , id) $ α.α X $ p }
    ; cong = λ { (e , q) → Func.cong (β.α X) (GT.trans (Func.cong (G.₁ _) (Func.cong (α.α X) q)) (G.F-resp-≈ (e , refl))) }
    }
  ; commute = λ { {X} {Y} f {x , y} →
      let open RS (H.₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ G.₁ (id ∘ x ∘ f , id) $ α.α X $ F.₁ (f , id) $ y ≈˘⟨ Func.cong (H.₁ _) (Func.cong (β.α X) ([ G ]-merge assoc id-0)) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (f , id) $ G.₁ (id ∘ x , id) $ α.α X $ F.₁ (f , id) $ y ≈⟨ β.commute f ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (id , f) $ G.₁ (id ∘ x , id) $ α.α X $ F.₁ (f , id) $ y
              ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) ([ G ]-resp-square (assoc , id-swap))) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (x ∘ id , id) $ G.₁ (id , f) $ α.α X $ F.₁ (f , id) $ y ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) (Func.cong (G.₁ _) (α.commute f))) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (x ∘ id , id) $ G.₁ (f , id) $ α.α Y $ F.₁ (id , f) $ y ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) ([ G ]-merge refl id-0)) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (f ∘ x ∘ id , id) $ α.α Y $ F.₁ (id , f) $ y ∎
    }
  } where
    module A = Category A
    open Reason A
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module FS {X} {Y} = RS (F.₀ (X , Y))
    module GS {X} {Y} = RS (G.₀ (X , Y))
    module HS {X} {Y} = RS (H.₀ (X , Y))
    module FT {X} {Y} = Setoid (F.₀ (X , Y))
    module GT {X} {Y} = Setoid (G.₀ (X , Y))
    module HT {X} {Y} = Setoid (H.₀ (X , Y))

-- Two-sided composition up-to loop.
compositionUpToLoop⁻⁺ : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation F G
  → DinaturalTransformation G H
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ F)) H
compositionUpToLoop⁻⁺ {A = A} {F = F} {G = G} {H = H} α β = dtHelper record
  { α = λ X → record
    { to = λ { (endo , p) → β.α X $ G.₁ (endo , endo) $ α.α X $ p }
    ; cong = λ { (e , q) → Func.cong (β.α X) (GT.trans (Func.cong (G.₁ _) (Func.cong (α.α X) q)) (G.F-resp-≈ (e , e))) }
    }
  ; commute = λ { {X} {Y} f {x , y} →
      let open RS (H.₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ G.₁ (id ∘ x ∘ f , id ∘ x ∘ f) $ α.α X $ F.₁ (f , id) $ y ≈˘⟨ Func.cong (H.₁ _) (Func.cong (β.α X) ([ G ]-merge assoc refl)) ⟩
            H.₁ (id , f) $ β.α X $ G.₁ (f , id) $ G.₁ (id ∘ x , x ∘ f) $ α.α X $ F.₁ (f , id) $ y ≈⟨ β.commute f ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (id , f) $ G.₁ (id ∘ x , x ∘ f) $ α.α X $ F.₁ (f , id) $ y ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) ([ G ]-resp-square (assoc , sym-assoc))) ⟩ -- (assoc ∙ skip (rw eq1) , skip (rw eq1) ∙ sym-assoc)
            H.₁ (f , id) $ β.α Y $ G.₁ (x ∘ id , f ∘ x) $ G.₁ (id , f) $ α.α X $ F.₁ (f , id) $ y ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) (Func.cong (G.₁ _) (α.commute f))) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (x ∘ id , f ∘ x) $ G.₁ (f , id) $ α.α Y $ F.₁ (id , f) $ y ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) ([ G ]-merge refl assoc)) ⟩
            H.₁ (f , id) $ β.α Y $ G.₁ (f ∘ x ∘ id , f ∘ x ∘ id) $ α.α Y $ F.₁ (id , f) $ y ∎
    }
  } where
    module A = Category A
    open Reason A
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module FS {X} {Y} = RS (F.₀ (X , Y))
    module GS {X} {Y} = RS (G.₀ (X , Y))
    module HS {X} {Y} = RS (H.₀ (X , Y))
    module FT {X} {Y} = Setoid (F.₀ (X , Y))
    module GT {X} {Y} = Setoid (G.₀ (X , Y))
    module HT {X} {Y} = Setoid (H.₀ (X , Y))
