{-# OPTIONS --safe --lossy-unification --without-K #-}

{-
Example of using loop-composition to validate the
implication elimination rule of natural deduction.
-}
module Dinaturals.ImplicationExample where

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
open import Categories.Functor.Hom using (Hom[_][-,-])

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

private
  variable
    o ℓ e : Level
    Γ : Category ℓ ℓ ℓ

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})

open import Dinaturals.Dinaturals
open import Dinaturals.LoopComposition

-- Loop-compositions to get the application rule up-to-loop.

eval-composite⁺ : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B))
  → DinaturalTransformation Φ A
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ Γ ][-,-] ※ Φ)) B
eval-composite⁺ {A = A} {B = B} {Φ = Φ} α β = compositionUpToLoop⁺ (productd β α) eval-din

eval-composite⁻ : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B))
  → DinaturalTransformation Φ A
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ Γ ][-,-] ※ Φ)) B
eval-composite⁻ {A = A} {B = B} {Φ = Φ} α β = compositionUpToLoop⁻ (productd β α) eval-din

eval-composite⁻⁺ : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B))
  → DinaturalTransformation Φ A
  → DinaturalTransformation (SetA.-×- ∘F (Hom[ Γ ][-,-] ※ Φ)) B
eval-composite⁻⁺ {A = A} {B = B} {Φ = Φ} α β = compositionUpToLoop⁻⁺ (productd β α) eval-din

infixr 5 _$_

private
  _$_ = _⟨$⟩_

-- Explicit dinaturality condition for covariant composition.

eval-composite⁺-condition : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → (α : DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))
  → (β : DinaturalTransformation Φ A)
  → (open Reason Γ)
  → (let module A = Functor A)
  → (let module B = Functor B)
  → (let module Φ = Functor Φ)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → {X Y : Obj} (f : X ⇒ Y) (g : Y ⇒ X) {v : Setoid.Carrier (Φ.F₀ (Y , X))} →
      Setoid._≈_ (B.F₀ (X , Y))

        (B.F₁ (id , f)
        $ B.F₁ (id , id ∘ g ∘ f)
        $ (α.α X $ Φ.F₁ (f , id) $ v)
        $ (A.F₁ (id ∘ g ∘ f , id)
        $ A.F₁ (id , id ∘ g ∘ f)
        $ (β.α X $ Φ.₁ (f , id) $ v)))

        (B.F₁ (f , id)
        $ B.F₁ (id , f ∘ g ∘ id)
        $ (α.α Y $ Φ.F₁ (id , f) $ v)
        $ (A.F₁ (f ∘ g ∘ id , id)
        $ A.F₁ (id , f ∘ g ∘ id)
        $ (β.α Y $ Φ.₁ (id , f) $ v)))
eval-composite⁺-condition {Γ = Γ} {A = A} {B = B} {Φ = Φ} α β f g {v = v} =
  DinaturalTransformation.commute (eval-composite⁺ {A = A} {B = B} {Φ = Φ} α β) f {x = g , v}
  where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module A = Functor A
    module B = Functor B
    module Φ = Functor Φ
    open Reason Γ

eval-composite⁻-condition : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → (α : DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))
  → (β : DinaturalTransformation Φ A)
  → (open Reason Γ)
  → (let module A = Functor A)
  → (let module B = Functor B)
  → (let module Φ = Functor Φ)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → {X Y : Obj} (f : X ⇒ Y) (g : Y ⇒ X) {v : Setoid.Carrier (Φ.F₀ (Y , X))} →
      Setoid._≈_ (B.F₀ (X , Y))

        (B.F₁ (id , f)
        $ B.F₁ (id ∘ g ∘ f  , id)
        $ (α.α X $ Φ.F₁ (f , id) $ v)
        $ (A.F₁ (id , id ∘ g ∘ f)
        $ A.F₁ (id ∘ g ∘ f , id)
        $ (β.α X $ Φ.₁ (f , id) $ v)))

        (B.F₁ (f , id)
        $ B.F₁ (f ∘ g ∘ id , id)
        $ (α.α Y $ Φ.F₁ (id , f) $ v)
        $ (A.F₁ (id , f ∘ g ∘ id)
        $ A.F₁ (f ∘ g ∘ id , id)
        $ (β.α Y $ Φ.₁ (id , f) $ v)))
eval-composite⁻-condition {Γ = Γ} {A = A} {B = B} {Φ = Φ} α β f g {v = v} =
    DinaturalTransformation.commute (eval-composite⁻ {A = A} {B = B} {Φ = Φ} α β) f {x = g , v}
  where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module A = Functor A
    module B = Functor B
    module Φ = Functor Φ
    open Reason Γ

eval-composite⁻⁺-condition : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → (α : DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))
  → (β : DinaturalTransformation Φ A)
  → (open Reason Γ)
  → (let module A = Functor A)
  → (let module B = Functor B)
  → (let module Φ = Functor Φ)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → {X Y : Obj} (f : X ⇒ Y) (g : Y ⇒ X) {v : Setoid.Carrier (Φ.F₀ (Y , X))} →
      Setoid._≈_ (B.F₀ (X , Y))

        (B.F₁ (id , f)
        $ B.F₁ (id ∘ g ∘ f , id ∘ g ∘ f)
        $ (α.α X $ Φ.F₁ (f , id) $ v)
        $ (A.F₁ (id ∘ g ∘ f , id ∘ g ∘ f)
        $ A.F₁ (id ∘ g ∘ f , id ∘ g ∘ f)
        $ (β.α X $ Φ.₁ (f , id) $ v)))

        (B.F₁ (f , id)
        $ B.F₁ (f ∘ g ∘ id , f ∘ g ∘ id)
        $ (α.α Y $ Φ.F₁ (id , f) $ v)
        $ (A.F₁ (f ∘ g ∘ id , f ∘ g ∘ id)
        $ A.F₁ (f ∘ g ∘ id , f ∘ g ∘ id)
        $ (β.α Y $ Φ.₁ (id , f) $ v)))
eval-composite⁻⁺-condition {Γ = Γ} {A = A} {B = B} {Φ = Φ} α β f g {v = v} =
   DinaturalTransformation.commute (eval-composite⁻⁺ {A = A} {B = B} {Φ = Φ} α β) f {x = g , v}
  where
    module α = DinaturalTransformation α
    module β = DinaturalTransformation β
    module A = Functor A
    module B = Functor B
    module Φ = Functor Φ
    open Reason Γ

-- Explicit description of the maps obtained by loop-composition.

eval-composite⁺-map : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → (α : DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))
  → (β : DinaturalTransformation Φ A)
  → (open Reason Γ)
  → (let module A = Functor A)
  → (let module B = Functor B)
  → (let module Φ = Functor Φ)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → {X Y : Obj} (f : X ⇒ X) {v : Setoid.Carrier (Φ.F₀ (X , X))} →
      Setoid._≈_ (B.F₀ (X , X))
           (DinaturalTransformation.α (eval-composite⁺ {A = A} {B = B} {Φ = Φ} α β) X ⟨$⟩ (f , v))
           (B.₁ (id , f) $ (α.α X $ v) $ A.₁ (f , id) $ A.₁ (id , f) $ β.α X $ v)
eval-composite⁺-map {Γ = Γ} {A = A} {B = B} {Φ = Φ} α β f {v = v} = Setoid.refl (Functor.F₀ B _)

eval-composite⁻-map : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → (α : DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))
  → (β : DinaturalTransformation Φ A)
  → (open Reason Γ)
  → (let module A = Functor A)
  → (let module B = Functor B)
  → (let module Φ = Functor Φ)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → {X Y : Obj} (f : X ⇒ X) {v : Setoid.Carrier (Φ.F₀ (X , X))} →
      Setoid._≈_ (B.F₀ (X , X))
           (DinaturalTransformation.α (eval-composite⁻ {A = A} {B = B} {Φ = Φ} α β) X ⟨$⟩ (f , v))
           (B.₁ (f , id) $ (α.α X $ v) $ A.₁ (id , f) $ A.₁ (f , id) $ β.α X $ v)
eval-composite⁻-map {Γ = Γ} {A = A} {B = B} {Φ = Φ} α β f {v = v} = Setoid.refl (Functor.F₀ B _)

eval-composite⁻⁺-map : {Γ : Category ℓ ℓ ℓ} {A B Φ : Functor (Product (Category.op Γ) Γ) (Setoids ℓ ℓ)}
  → (α : DinaturalTransformation Φ (Set.-⇨- ∘F (Functor.op A ∘F Swap ※ B)))
  → (β : DinaturalTransformation Φ A)
  → (open Reason Γ)
  → (let module A = Functor A)
  → (let module B = Functor B)
  → (let module Φ = Functor Φ)
  → (let module α = DinaturalTransformation α)
  → (let module β = DinaturalTransformation β)
  → {X Y : Obj} (f : X ⇒ X) {v : Setoid.Carrier (Φ.F₀ (X , X))} →
      Setoid._≈_ (B.F₀ (X , X))
           (DinaturalTransformation.α (eval-composite⁻⁺ {A = A} {B = B} {Φ = Φ} α β) X ⟨$⟩ (f , v))
           (B.₁ (f , f) $ (α.α X $ v) $ (A.₁ (f , f) $ A.₁ (f , f) $ β.α X $ v))
eval-composite⁻⁺-map {Γ = Γ} {A = A} {B = B} {Φ = Φ} α β f {v = v} = Setoid.refl (Functor.F₀ B _)
