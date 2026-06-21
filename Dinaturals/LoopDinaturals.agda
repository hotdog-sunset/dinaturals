{-# OPTIONS --safe --without-K #-}

{-
A loop dinatural is a dinatural of the form hom(x,x) x F(x,x) -> G(x,x).

Loop dinaturals compose using loop-composition (in their different flavours).

We define such composition and use it to define the category of functors Aᵒᵖ × A → Setoids,
with loop-dinatural transformations as morphisms.
-}
module Dinaturals.LoopDinaturals where

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


{-
Covariant, contravariant and two-sided composition of loop dinaturals all take the following shape:

hom(x,x) x F(x,x) -> G(x,x)      hom(x,x) x G(x,x) -> H(x,x)
------------------------------------------------------------
              hom(x,x) x F(x,x) -> H(x,x)
-}

LoopDinaturalTransformation : ∀ {o} {A : Category o ℓ ℓ} (F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)) → Set (sucℓ ℓ ⊔ o)
LoopDinaturalTransformation {A = A} F G = DinaturalTransformation (SetA.-×- ∘F (Hom[ A ][-,-] ※ F)) G

-- Covariant composition between loop-dinaturals.
loopComposition⁺  : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → LoopDinaturalTransformation F G
  → LoopDinaturalTransformation G H
  → LoopDinaturalTransformation F H
loopComposition⁺ {A = A} {F = F} {G = G} {H = H} α β = dtHelper record
  { α = λ X → record
    { to = λ { (endo , p) → β.α X $ (endo , G.₁ (id , endo) $ α.α X $ (endo , p)) }
    ; cong = λ { (e , q) → Func.cong (β.α X) (e , GT.trans (G.F-resp-≈ (refl , e)) (Func.cong (G.₁ _) (Func.cong (α.α _) (e , q)))) }
    }
  ; commute = λ { {X} {Y} f {x , v} →
      let open RS (H.₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (id , id ∘ x ∘ f) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈˘⟨ Func.cong (H.₁ _) (Func.cong (β.α X) (refl , [ G ]-merge id-0 assoc)) ⟩
            H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (id , id ∘ x) $ G.₁ (id , f) $ (α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v))) ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α X) (refl , Func.cong (G.₁ _) (α.commute f))) ⟩
            H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (id , id ∘ x) $ G.₁ (f , id) $ (α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v))) ≈⟨ Func.cong (H.₁ (id , f)) (Func.cong (β.α X) (refl , [ G ]-resp-square (id-swap , assoc))) ⟩
            H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (f , id) $ G.₁ (id , x ∘ id) $ (α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v))) ≈⟨ β.commute f ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (id , f) $ G.₁ (id , x ∘ id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ≈⟨ Func.cong (H.F₁ (f , id)) (Func.cong (β.α Y) (refl , [ G ]-merge id-1 refl)) ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (id , f ∘ x ∘ id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ∎
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

-- Contravariant composition between loop-dinaturals.
loopComposition⁻ : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → LoopDinaturalTransformation F G
  → LoopDinaturalTransformation G H
  → LoopDinaturalTransformation F H
loopComposition⁻ {A = A} {F = F} {G = G} {H = H} α β = dtHelper record
  { α = λ X → record
    { to = λ { (endo , p) → β.α X $ (endo , G.₁ (endo , id) $ α.α X $ (endo , p)) }
    ; cong = λ { (e , q) → Func.cong (β.α X) (e , GT.trans (G.F-resp-≈ (e , refl)) (Func.cong (G.₁ _) (Func.cong (α.α _) (e , q)))) }
    }
  ; commute = λ { {X} {Y} f {x , v} →
      let open RS (H.₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (id ∘ x ∘ f , id) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈˘⟨ Func.cong (H.₁ _) (Func.cong (β.α X) (refl , [ G ]-merge assoc id-0)) ⟩ -- [ G ]-merge id-0 assoc
            H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (f , id) $ G.₁ (id ∘ x , id) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈⟨ β.commute f ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (id , f) $ G.₁ (id ∘ x , id) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈⟨ Func.cong (H.₁ (f , id)) (Func.cong (β.α Y) (refl , [ G ]-resp-square (assoc , id-swap))) ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (x ∘ id , id) $ G.₁ (id , f) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈⟨ Func.cong (H.F₁ (f , id)) (Func.cong (β.α Y) (refl , Func.cong (G.₁ (x ∘ id , id)) (α.commute f {x = x , v}))) ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (x ∘ id , id) $ G.₁ (f , id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ≈⟨ Func.cong (H.F₁ (f , id)) (Func.cong (β.α Y) (refl , [ G ]-merge refl id-0)) ⟩  --{!   !} ≈⟨ {!   !} ⟩ -- H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (id , f) $ G.₁ (id , x ∘ id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ≈⟨ Func.cong (H.F₁ (f , id)) (Func.cong (β.α Y) (refl , [ G ]-merge id-1 refl)) ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (f ∘ x ∘ id , id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ∎
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

-- Two-sided composition between loop-dinaturals.
loopComposition⁻⁺ : ∀ {o} {A : Category o ℓ ℓ} {F G H : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → LoopDinaturalTransformation F G
  → LoopDinaturalTransformation G H
  → LoopDinaturalTransformation F H
loopComposition⁻⁺ {A = A} {F = F} {G = G} {H = H} α β = dtHelper record
  { α = λ X → record
    { to = λ { (endo , p) → β.α X $ (endo , G.₁ (endo , endo) $ α.α X $ (endo , p)) }
    ; cong = λ { (e , q) → Func.cong (β.α X) (e , GT.trans (G.F-resp-≈ (e , e)) (Func.cong (G.₁ _) (Func.cong (α.α _) (e , q)))) }
    }
  ; commute = λ { {X} {Y} f {x , v} →
      let open RS (H.₀ (X , Y)) in
      begin H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (id ∘ x ∘ f , id ∘ x ∘ f) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈˘⟨ Func.cong (H.₁ _) (Func.cong (β.α X) (refl , GT.trans ([ G ]-merge refl refl) ([ G ]-merge refl assoc))) ⟩
            H.₁ (id , f) $ β.α X $ (id ∘ x ∘ f , G.₁ (f , id) $ G.₁ (x , x) $ G.₁ (id , f) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈⟨ β.commute f {x = x , _} ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (id , f) $ G.₁ (x , x) $ G.₁ (id , f) $ α.α X $ (id ∘ x ∘ f , F.₁ (f , id) $ v)) ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) (refl , Func.cong (G.₁ _) (Func.cong (G.₁ _) (α.commute f)))) ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (id , f) $ G.₁ (x , x) $ G.₁ (f , id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ≈⟨ Func.cong (H.₁ _) (Func.cong (β.α Y) (refl , GT.trans ([ G ]-merge refl refl) ([ G ]-merge refl assoc))) ⟩
            H.₁ (f , id) $ β.α Y $ (f ∘ x ∘ id , G.₁ (f ∘ x ∘ id , f ∘ x ∘ id) $ α.α Y $ (f ∘ x ∘ id , F.₁ (id , f) $ v)) ∎
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

-----------------------------------------------------------------------------------------

-- Associativity on the nose for all three compositions.

loopComposition⁺-assoc : ∀ {o} {A : Category o ℓ ℓ} {F G H E : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → (α : LoopDinaturalTransformation F G)
  → (β : LoopDinaturalTransformation G H)
  → (g : LoopDinaturalTransformation H E)
  → loopComposition⁺ {A = A}  {F = F} {G = G} α (loopComposition⁺ {A = A} {F = G} {G = H} β g)
  ≃ᵈ loopComposition⁺ {A = A} {F = F} {G = H} (loopComposition⁺ {A = A} {F = F} {G = G} α β) g
loopComposition⁺-assoc {E = E} α β g = ES.refl where
    module E = Functor E
    module ES {X} {Y} = Setoid (E.₀ (X , Y))

loopComposition⁻-assoc : ∀ {o} {A : Category o ℓ ℓ} {F G H E : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → (α : LoopDinaturalTransformation F G)
  → (β : LoopDinaturalTransformation G H)
  → (g : LoopDinaturalTransformation H E)
  → loopComposition⁻ {A = A}  {F = F} {G = G} α (loopComposition⁻ {A = A} {F = G} {G = H} β g)
  ≃ᵈ loopComposition⁻ {A = A} {F = F} {G = H} (loopComposition⁻ {A = A} {F = F} {G = G} α β) g
loopComposition⁻-assoc {E = E} α β g = ES.refl where
    module E = Functor E
    module ES {X} {Y} = Setoid (E.₀ (X , Y))

loopComposition⁻⁺-assoc : ∀ {o} {A : Category o ℓ ℓ} {F G H E : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → (α : LoopDinaturalTransformation F G)
  → (β : LoopDinaturalTransformation G H)
  → (g : LoopDinaturalTransformation H E)
  → loopComposition⁻⁺ {A = A}  {F = F} {G = G} α (loopComposition⁻⁺ {A = A} {F = G} {G = H} β g)
  ≃ᵈ loopComposition⁻⁺ {A = A} {F = F} {G = H} (loopComposition⁻⁺ {A = A} {F = F} {G = G} α β) g
loopComposition⁻⁺-assoc {E = E} α β g = ES.refl where
    module E = Functor E
    module ES {X} {Y} = Setoid (E.₀ (X , Y))

-----------------------------------------------------------------------------------------

-- Loop-equivalence: two loop-dinaturals are related if they are pointwise equal
-- when applied (not composed as dinaturals) to the identity endomorphisms.
loopEquiv : ∀ {o} {A : Category o ℓ ℓ} {F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
  → (α β : LoopDinaturalTransformation F G)
  → Set (ℓ ⊔ o)
loopEquiv {A = A} {F = F} {G = G} α β =
  ∀ {X} {v : Setoid.Carrier (F.₀ (X , X))} →
    Setoid._≈_ (G.₀ (X , X)) (α.α X $ (id , v)) (β.α X $ (id , v)) where
  module A = Category A
  open Reason A
  module F = Functor F
  module G = Functor G
  module α = DinaturalTransformation α
  module β = DinaturalTransformation β
  module FS {X} {Y} = RS (F.₀ (X , Y))
  module GS {X} {Y} = RS (G.₀ (X , Y))
  module FT {X} {Y} = Setoid (F.₀ (X , Y))
  module GT {X} {Y} = Setoid (G.₀ (X , Y))

-- Loop-equivalence is an equivalence relation.
loopEquiv-IsEquivalence : ∀ {o} {A : Category o ℓ ℓ} {F G : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
   → IsEquivalence (loopEquiv {F = F} {G = G})
loopEquiv-IsEquivalence {A = A} {F = F} {G = G} = record
  { refl = GT.refl
  ; sym = λ e → GT.sym e
  ; trans = λ e₁ e₂ → GT.trans e₁ e₂
  } where
  module A = Category A
  open Reason A
  module G = Functor G
  module GT {X} {Y} = Setoid (G.₀ (X , Y))

-- The identity loop-dinatural which simply forgets the endomorphism.
id-π₂ :  ∀ {o} {A : Category o ℓ ℓ} {F : Functor (op A ⊗ A) (Setoids ℓ ℓ)}
    → LoopDinaturalTransformation F F
id-π₂ {ℓ = ℓ} {A = A} {F = F} = dtHelper (record
  { α = λ X → proj₂ₛ
  ; commute = λ f → [ F ]-commute
  }) where
  module A = Category A
  open Reason A
  module F = Functor F
  module FS {X} {Y} = RS (F.₀ (X , Y))
  module FT {X} {Y} = Setoid (F.₀ (X , Y))

-- Category of functors Aᵒᵖ × A → Setoids, with hom×- dinatural transformations as morphisms and covariant loop composition.
loop-dinats⁺ :  ∀ {o} {A : Category o ℓ ℓ} → Category (sucℓ ℓ ⊔ o) (sucℓ ℓ ⊔ o) (ℓ ⊔ o)
loop-dinats⁺ {ℓ = ℓ} {A = A} = categoryHelper record
  { Obj = Functor (op A ⊗ A) (Setoids ℓ ℓ)
  ; _⇒_ = LoopDinaturalTransformation
  ; _≈_ = loopEquiv
  ; id = id-π₂
  ; _∘_ = λ f g → loopComposition⁺ g f
  ; assoc = λ {F} {G} {H} {E} {X = X} {v} →
    let module E = Functor E in
     Setoid.refl (E.₀ (X , X))
  ; identityˡ = λ {F} {G} {f} {X} {v} →
    let module G = Functor G in
    G.identity
  ; identityʳ = λ {F} {G} {f} {X} {v} →
    let module F = Functor F
        module G = Functor G
        module f = DinaturalTransformation f
        open Category A in
    Func.cong (f.α X) (Equiv.refl , F.identity)
  ; equiv = loopEquiv-IsEquivalence
  ; ∘-resp-≈ = λ {F} {G} {H} {f} {h} {g} {i} p q →
     let open Category A
         module h = DinaturalTransformation h
         module FT {X} {Y} = Setoid (Functor.F₀ F (X , Y))
         module GT {X} {Y} = Setoid (Functor.F₀ G (X , Y))
         module HT {X} {Y} = Setoid (Functor.F₀ H (X , Y)) in
        HT.trans p (Func.cong (h.α _) (Equiv.refl , Func.cong (F₁ G (id , id)) q))
  }
