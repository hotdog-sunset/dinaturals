{-# OPTIONS --safe --without-K #-}

{-
We formalize a result by Freyd: if all Set-valued dinaturals for functors C^op x C -> Set compose (pointwisely), then C is a groupoid.
-}
module Dinaturals.ComposeGroupoid where

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

open import Relation.Binary.Structures using (IsEquivalence)

open Functor using (homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

open import Dinaturals.IsDinatural

import Reason

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record SetoidEquivalence (A B : Setoid ℓ ℓ) : Set ℓ where
  private
    module A = Setoid A
    module B = Setoid B
  field
    to      : A.Carrier → B.Carrier
    from    : B.Carrier → A.Carrier

-- The setoid of setoids with logical equivalence as equality.
SetoidOfSetoids : Setoid (sucℓ ℓ) ℓ
SetoidOfSetoids {ℓ = ℓ} = record
  { Carrier = Setoid ℓ ℓ
  ; _≈_ = SetoidEquivalence
  ; isEquivalence = record
    { refl = record
      { to = λ z → z
      ; from = λ z → z
      }
    ; sym = λ i → record
      { to = SetoidEquivalence.from i
      ; from = SetoidEquivalence.to i
      }
    ; trans = λ i j → record
      { to = λ z → j .SetoidEquivalence.to (i .SetoidEquivalence.to z)
      ; from = λ z → i .SetoidEquivalence.from (j .SetoidEquivalence.from z)
      }
    }
  }

-- The covariant powerset functor, with direct image as action on morphisms.
powerset : Functor (Setoids ℓ ℓ) (Setoids (sucℓ ℓ) ℓ)
powerset {ℓ = ℓ} = record
  { F₀ = λ A → FunctionSetoid A SetoidOfSetoids
  ; F₁ = λ {A} {B} f →
  let module A = Setoid A
      module B = Setoid B in
    record
      { to = λ P → record
        { to = λ b → record
          { Carrier = ∃[ t ] Setoid._≈_ B (f ⟨$⟩ t) b × Setoid.Carrier (P ⟨$⟩ t)
          ; _≈_ = λ { (t₁ , _ , _) (t₂ , _ , _) → t₁ A.≈ t₂ }
          ; isEquivalence = record
            { refl = A.refl
            ; sym = A.sym
            ; trans = A.trans
            }
          }
        ; cong = λ x → record
          { to = λ { (a , e , p) → a , B.trans e x , p }
          ; from = λ { (a , e , p) → a , B.trans e (B.sym x) , p }
          }
        }
      ; cong = λ e v → record
        { to = λ { (a , eq , p) → a , eq , SetoidEquivalence.to (e _) p }
        ; from = λ { (a , eq , p) → a , eq , SetoidEquivalence.from (e _) p }
        }
      }
  ; identity = λ { {X} {P} →
    λ x → record
      { to = λ { (a , j , o) → SetoidEquivalence.to (Func.cong P j) o }
      ; from = λ p → x , Setoid.refl X , p
      }
    }
  ; homomorphism = λ {X} {Y} {Z} {f} {g} v → record
    { to = λ { (a , j , o) → f ⟨$⟩ a , j , a , Setoid.refl Y , o }
    ; from = λ { (i , u , k , e , r) → k , Setoid.trans Z (Func.cong g e) u , r }
    }
  ; F-resp-≈ = λ {X} {Y} {f} {g} i p → record
    { to = λ { (a , j , o) → a , Setoid.trans Y (Setoid.sym Y i) j , o }
    ; from = λ { (a , u , e) → a , Setoid.trans Y i u , e }
    }
  }

-- Inclusion of small setoids into large setoids.
inclusion : Functor (Setoids ℓ ℓ) (Setoids (sucℓ ℓ) ℓ)
inclusion = record
  { F₀ = λ X →
    let open Setoid X in
    record
    { Carrier = Lift (sucℓ _) Carrier
    ; _≈_ = λ { (lift a) (lift b) → a ≈ b }
    ; isEquivalence = record
      { refl = Setoid.refl X
      ; sym = Setoid.sym X
      ; trans = Setoid.trans X
      }
    }
  ; F₁ = λ f → record
    { to = λ { (lift x) → lift (f ⟨$⟩ x) }
    ; cong = λ { t → Func.cong f t }
    }
  ; identity = λ {A} → Setoid.refl A
  ; homomorphism = λ {_} {_} {Z} → Setoid.refl Z
  ; F-resp-≈ = λ h → h
  }

-- The terminal setoid, which we redefine because agda-stdlib setoids are not level polymorphic in both object and equality levels.
UnitSetoid : Setoid (sucℓ ℓ) ℓ
UnitSetoid = alwaysSetoid ⊤ _

-- The identity dinatural but lifted to large setoids.
refl-with-inclusion : ∀ {o} (A : Category o ℓ ℓ)
     → DinaturalTransformation
          (const {D = Setoids (sucℓ ℓ) ℓ} {C = Product (Category.op A) A} UnitSetoid)
          (inclusion ∘F Hom[ A ][-,-])
refl-with-inclusion A =
  let open Reason A in
    dtHelper record
    { α = λ X → record
      { to = λ x → lift id
      ; cong = λ x → refl
      }
    ; commute = λ f → id-swap-2
    }

-- The solutions dinatural, which has large sets as codomain.
solutions : ∀ {o} (A : Category o ℓ ℓ) (C : Category.Obj A)
     → DinaturalTransformation (inclusion ∘F Hom[ A ][-,-]) (powerset ∘F Hom[ A ][ C ,-] ∘F πʳ)
solutions {ℓ = ℓ} A C =
  let open Reason A in
  dtHelper record
  { α = λ X → record
    { to = λ { (lift e) → record
      { to = λ f → alwaysSetoid (f ≈ e ∘ f) ℓ
      ; cong = λ e → record
        { to = λ q → Equiv.trans (Equiv.trans (Equiv.sym e) q) (∘-resp-≈ʳ e)
        ; from = λ q → Equiv.trans (Equiv.trans e q) (∘-resp-≈ʳ (Equiv.sym e))
        }
      } }
    ; cong = λ { x q → record
      { to = λ e → Equiv.trans e (∘-resp-≈ˡ x)
      ; from = λ e → Equiv.trans e (∘-resp-≈ˡ (Equiv.sym x))
      } }
    }
  ; commute = λ f →
    λ { {lift l} x → record
        { to = λ { (o , e , g) →
          x , (id-0 ∙ id-1)
            , (sym e ∙ skip (rw g)
            ∙ skip assoc
            ∙ skip assoc-3
            ∙ sym-assoc-3 ∙ rw (skip sym-id-swap)
            ∙ sym (skip (sym e))) }
        ; from = λ { (o , e , g) →
          (l ∘ o) , (((skip assoc ∙ skip-2 id-swap ∙ sym-assoc-3) ∙ ((sym g ∙ sym-id-1) ∙ sym-id-0)) ∙ e)
                  , (skip g ∙ (skip assoc-3 ∙ sym-id-0 ∙ (sym-assoc-3 ∙ skip idm-1))) }
        }
      }
  }

-- Main theorem: if all Set-valued dinaturals for functors C^op x C -> Set compose (pointwisely), then C is a groupoid.
groupoid-dinaturals-compose : ∀ {C : Category o ℓ ℓ}
  → AllDinaturalsCompose C (Setoids (sucℓ ℓ) ℓ)
  → IsGroupoid C
groupoid-dinaturals-compose {ℓ = ℓ} {C = C} dc =
  let open Reason C
      -- The "raw" dinaturality condition given by composing solutions dinatural with refl-with-inclusion.
      dinaturality-condition : ∀ (B : Obj) →
        IsDinaturalFamily (const UnitSetoid)
            (powerset ∘F Hom[ C ][ B ,-] ∘F πʳ)
            (λ X →
              (Setoids (sucℓ ℓ) ℓ Category.∘
                DinaturalTransformation.α (solutions C B) X)
              (DinaturalTransformation.α (refl-with-inclusion C) X))
      dinaturality-condition B =
        dc {F = (const {D = Setoids (sucℓ ℓ) ℓ} {C = Product (Category.op C) C} UnitSetoid)}
            {G = (inclusion ∘F Hom[ C ][-,-])}
            {H = (powerset ∘F Hom[ C ][ B ,-] ∘F πʳ)}
            (refl-with-inclusion C) (solutions C B)

      -- "Polished" version of the above condition to derive that every morphism has a left inverse.
      every-map-is-left-invertible : ∀ {A B : Obj} → (f : C [ A , B ]) → Σ[ t ∈ B ⇒ A ] f ∘ t ≈ id
      every-map-is-left-invertible f =
        let aux : ∀ {A B : Obj} → (f : C [ A , B ]) → Σ[ t ∈ B ⇒ A ] f ∘ t ∘ id ≈ id × t ≈ id ∘ t
            aux {A = A} {B = B} f = SetoidEquivalence.from (dinaturality-condition B f {x = tt} id) (id , id2 , sym-id-0)
         in proj₁ (aux f) , (sym-id-2 ∙ proj₁ (proj₂ (aux f)))
     in
  record
    { _⁻¹ = λ f → proj₁ (every-map-is-left-invertible f)
    ; iso = λ {X} {Y} {f} → record
      { isoˡ =
            -- We iterate the every-map-is-left-invertible twice, first to get a left inverse g for f, and then to get a left inverse h for g, and then prove h = f.
        let inverse-unique : f ≈ proj₁ (every-map-is-left-invertible (proj₁ (every-map-is-left-invertible f)))
            inverse-unique =
              sym-id-1 ∙
              skip (sym (proj₂ (every-map-is-left-invertible (proj₁ (every-map-is-left-invertible f))))) ∙
              rw-2-1 (proj₂ (every-map-is-left-invertible f)) ∙ id-0
              in
           skip inverse-unique ∙ proj₂ (every-map-is-left-invertible (proj₁ (every-map-is-left-invertible f)))
      ; isoʳ = proj₂ (every-map-is-left-invertible f)
      }
    }
