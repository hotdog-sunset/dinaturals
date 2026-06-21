{-# OPTIONS --safe --without-K #-}

{-
There is a monoid object in the category of functors (C^op x C) -> Set, given by Hom[ C ][-,-].
This induces a writer-like monad where the unit is given by refl and multiplication is given by composition.
-}
module Dinaturals.CompositionMonad where

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
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)

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

-- Tensoring with hom is functorial.
functoriality : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation F G
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ F)) (SetA.-×- ∘F (Hom[ A ][-,-] ※ G))
functoriality {A = A} {F = F} {G = G} {H = H} α = dtHelper record
  { α = λ X → record
    { to = λ { (e , a) → e , α.α X $ a }
    ; cong = λ { (e , a) → e , Func.cong (α.α _) a }
    }
  ; commute = λ { {X} {Y} f {e , v} → (let open HomReasoning in
          begin f ∘ (id ∘ e ∘ f) ∘ id ≈⟨ id-2 ⟩
                f ∘ id ∘ e ∘ f ≈⟨ sym-assoc-3 ⟩
                (f ∘ id ∘ e) ∘ f ≈⟨ rw (skip sym-id-swap) ⟩
                (f ∘ e ∘ id) ∘ f ≈⟨ sym-id-0 ⟩
                id ∘ (f ∘ e ∘ id) ∘ f ∎) , α.commute f }
  } where
    module A = Category A
    open Reason A
    module α = DinaturalTransformation α
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module FS {X} {Y} = RS (F.₀ (X , Y))
    module GS {X} {Y} = RS (G.₀ (X , Y))
    module HS {X} {Y} = RS (H.₀ (X , Y))
    module FT {X} {Y} = Setoid (F.₀ (X , Y))
    module GT {X} {Y} = Setoid (G.₀ (X , Y))
    module HT {X} {Y} = Setoid (H.₀ (X , Y))

-- The unit of the monad, given by taking the product between refl and the identity dinatural.
η : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation F (SetA.-×- ∘F (Hom[ A ][-,-] ※ F))
η {A = A} {F = F} {G = G} {H = H} = dtHelper record
  { α = λ X → record
    { to = λ { a → id , a }
    ; cong = λ x → refl , x
    }
  ; commute = λ { {X} {Y} f {e} → id-swap-2 , [ F ]-commute }
  } where
    module A = Category A
    open Reason A
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module FS {X} {Y} = RS (F.₀ (X , Y))
    module GS {X} {Y} = RS (G.₀ (X , Y))
    module HS {X} {Y} = RS (H.₀ (X , Y))
    module FT {X} {Y} = Setoid (F.₀ (X , Y))
    module GT {X} {Y} = Setoid (G.₀ (X , Y))
    module HT {X} {Y} = Setoid (H.₀ (X , Y))

-- Multiplication map, given by composition of endomorphisms.
μ : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ (SetA.-×- ∘F (Hom[ A ][-,-] ※ F))))
                            (SetA.-×- ∘F (Hom[ A ][-,-] ※ F))
μ {A = A} {F = F} {G = G} {H = H} = dtHelper record
  { α = λ X → record
    { to = λ { (f , g , a) → f ∘ g , a }
    ; cong = λ { (f , g , a) → ∘-resp-≈ f g , a }
    }
  ; commute = λ { {X} {Y} h {f , g , v} →
      (let open HomReasoning in
          begin h ∘ ((id ∘ f ∘ h) ∘ id ∘ g ∘ h) ∘ id ≈⟨ id-2 ⟩
                h ∘ (id ∘ f ∘ h) ∘ id ∘ g ∘ h ≈⟨ skip (assoc ∙ (id-0 ∙ assoc)) ⟩
                h ∘ f ∘ h ∘ id ∘ g ∘ h ≈⟨ sym-assoc-2 ⟩
                (h ∘ f) ∘ h ∘ id ∘ g ∘ h ≈⟨ rw sym-id-2 ⟩
                (h ∘ f ∘ id) ∘ h ∘ id ∘ g ∘ h ≈⟨ skip (skip (rw-2 sym-id-swap)) ⟩
                (h ∘ f ∘ id) ∘ h ∘ g ∘ id ∘ h ≈⟨ sym-assoc-4 ⟩
                ((h ∘ f ∘ id) ∘ h ∘ g ∘ id) ∘ h ≈⟨ sym-id-0 ⟩
                id ∘ ((h ∘ f ∘ id) ∘ h ∘ g ∘ id) ∘ h ∎) , [ F ]-commute
    }
  } where
    module A = Category A
    open Reason A
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module FS {X} {Y} = RS (F.₀ (X , Y))
    module GS {X} {Y} = RS (G.₀ (X , Y))
    module HS {X} {Y} = RS (H.₀ (X , Y))
    module FT {X} {Y} = Setoid (F.₀ (X , Y))
    module GT {X} {Y} = Setoid (G.₀ (X , Y))
    module HT {X} {Y} = Setoid (H.₀ (X , Y))
