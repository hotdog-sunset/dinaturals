{-# OPTIONS --safe --without-K #-}

{-
  We encode a combinatorial example of two dinaturals not composing, using NonTrivialEndo.
-}
module Dinaturals.NonCompositionalityExample where

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to zeroℓ; suc to sucℓ)

import Data.Unit
open import Categories.Category
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.Construction.Functors using (Functors; eval; curry; uncurry)
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
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Identity renaming (function to idS)
open import Function.Construct.Composition using (function)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.Always using () renaming (setoid to alwaysSetoid)

open import Data.Bool using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to discreteSetoid)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

import Reason

open import Dinaturals.IsDinatural
open import Interval
open import NonTrivialEndo

private
  variable
    o ℓ e : Level
    A B C Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

F : Functor (Product (op Interval) Interval) NonTrivialEndo
F = record
  { F₀ = λ { _ → 0F }
  ; F₁ = λ { _ → 0F }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ _ → refl
  }

G : Functor (Product (op Interval) Interval) NonTrivialEndo
G = record
  { F₀ = λ { _ → 0F }
  ; F₁ = λ { {0F , 0F} {0F , 0F} (0F , 0F) → 0F
           ; {1F , 1F} {1F , 1F} (0F , 0F) → 0F
           ; {0F , 1F} {0F , 1F} (0F , 0F) → 0F
           ; {1F , 0F} {1F , 0F} (0F , 0F) → 0F

           ; {0F , 0F} {0F , 1F} (0F , 0F) → 0F
           ; {1F , 0F} {0F , 0F} (0F , 0F) → 1F
           ; {1F , 1F} {0F , 1F} (0F , 0F) → 0F
           ; {1F , 0F} {1F , 1F} (0F , 0F) → 1F

           ; {1F , 0F} {0F , 1F} (0F , 0F) → 1F

           ; {0F , 0F} {1F , 0F} (() , 0F)
           ; {0F , 0F} {1F , 1F} (() , 0F)
           ; {0F , 1F} {1F , 1F} (() , 0F)
           }
  ; identity = λ { {0F , 0F} → refl
                 ; {0F , 1F} → refl
                 ; {1F , 0F} → refl
                 ; {1F , 1F} → refl }
  ; homomorphism = λ { {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} → refl

                     ; {1F , 0F} {0F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {0F , 0F} {0F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 1F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {0F , 0F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {0F , 1F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 1F} {1F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl

                     ; {1F , 0F} {1F , 0F} {1F , 0F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 0F} {1F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 1F} {1F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 1F} {1F , 1F} {1F , 1F} {0F , 0F} {0F , 0F} → refl

                     ; {0F , 0F} {0F , 0F} {1F , 0F} {_ , _} {() , _}
                     ; {0F , 0F} {0F , 0F} {1F , 1F} {_ , _} {() , _}
                     ; {0F , 0F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {0F , 1F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {1F , 0F} {0F , 0F} {1F , 0F} {_ , _} {() , _}
                     ; {1F , 0F} {0F , 0F} {1F , 1F} {_ , _} {() , _}
                     ; {1F , 0F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {1F , 1F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {0F , 0F} {1F , _} {1F , 0F} {() , _} {_ , _}
                     ; {0F , 1F} {1F , _} {1F , 0F} {() , _} {_ , _}
                     ; {0F , 0F} {1F , _} {_ , 1F} {() , _} {_ , _}
                     ; {0F , 1F} {1F , _} {_ , 1F} {() , _} {_ , _}
                     }
  ; F-resp-≈ = λ { {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {1F , 0F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {0F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {1F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 1F} {1F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {0F , 0F} {1F , 0F} {() , 0F} {_ , 0F} (refl , refl)
                 ; {0F , 0F} {1F , 1F} {() , 0F} {_ , 0F} (refl , refl)
                 ; {0F , 1F} {1F , 1F} {() , 0F} {_ , 0F} (refl , refl)
                 }
  }

H : Functor (Product (op Interval) Interval) NonTrivialEndo
H = record
  { F₀ = λ { _ → 0F }
  ; F₁ = λ { {0F , 0F} {0F , 0F} (0F , 0F) → 0F
           ; {1F , 1F} {1F , 1F} (0F , 0F) → 0F
           ; {0F , 1F} {0F , 1F} (0F , 0F) → 0F
           ; {1F , 0F} {1F , 0F} (0F , 0F) → 0F

           ; {0F , 0F} {0F , 1F} (0F , 0F) → 1F
           ; {1F , 1F} {0F , 1F} (0F , 0F) → 0F

           ; {1F , 0F} {0F , 0F} (0F , 0F) → 0F
           ; {1F , 0F} {0F , 1F} (0F , 0F) → 1F
           ; {1F , 0F} {1F , 1F} (0F , 0F) → 1F

           ; {0F , 0F} {1F , 0F} (() , 0F)
           ; {0F , 0F} {1F , 1F} (() , 0F)
           ; {0F , 1F} {1F , 1F} (() , 0F)
           }
  ; identity = λ { {0F , 0F} → refl
                 ; {0F , 1F} → refl
                 ; {1F , 0F} → refl
                 ; {1F , 1F} → refl }
  ; homomorphism = λ { {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} → refl

                     ; {1F , 0F} {0F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {0F , 0F} {0F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 1F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {0F , 0F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {0F , 1F} {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 1F} {1F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} → refl

                     ; {1F , 0F} {1F , 0F} {1F , 0F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 0F} {1F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 0F} {1F , 1F} {1F , 1F} {0F , 0F} {0F , 0F} → refl
                     ; {1F , 1F} {1F , 1F} {1F , 1F} {0F , 0F} {0F , 0F} → refl

                     ; {0F , 0F} {0F , 0F} {1F , 0F} {_ , _} {() , _}
                     ; {0F , 0F} {0F , 0F} {1F , 1F} {_ , _} {() , _}
                     ; {0F , 0F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {0F , 1F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {1F , 0F} {0F , 0F} {1F , 0F} {_ , _} {() , _}
                     ; {1F , 0F} {0F , 0F} {1F , 1F} {_ , _} {() , _}
                     ; {1F , 0F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {1F , 1F} {0F , 1F} {1F , 1F} {_ , _} {() , _}
                     ; {0F , 0F} {1F , _} {1F , 0F} {() , _} {_ , _}
                     ; {0F , 1F} {1F , _} {1F , 0F} {() , _} {_ , _}
                     ; {0F , 0F} {1F , _} {_ , 1F} {() , _} {_ , _}
                     ; {0F , 1F} {1F , _} {_ , 1F} {() , _} {_ , _}
                     }
  ; F-resp-≈ = λ { {0F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {0F , 0F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {1F , 0F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {0F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {0F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 1F} {0F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 0F} {1F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {1F , 1F} {1F , 1F} {0F , 0F} {0F , 0F} (refl , refl) → refl
                 ; {0F , 0F} {1F , 0F} {() , 0F} {_ , 0F} (refl , refl)
                 ; {0F , 0F} {1F , 1F} {() , 0F} {_ , 0F} (refl , refl)
                 ; {0F , 1F} {1F , 1F} {() , 0F} {_ , 0F} (refl , refl)
                 }
  }

-- We pick always the identity functions for both functions α and β.
α : DinaturalTransformation F G
α = dtHelper record
  { α = λ X → 0F
  ; commute = λ { {0F} {0F} 0F → refl
                ; {0F} {1F} 0F → refl
                ; {1F} {1F} 0F → refl }
  }

β : DinaturalTransformation G H
β = dtHelper record
  { α = λ X → 0F
  ; commute = λ { {0F} {0F} 0F → refl
                ; {0F} {1F} 0F → refl
                ; {1F} {1F} 0F → refl }
  }

0≠1 : ∀ {n} → ¬ (1F ≡ Fin.zero {n = ℕ.suc n}  )
0≠1 ()

-- The composition of α and β is not dinatural.
do-not-compose : ¬ CompositionIsDinatural α β
do-not-compose comp = 0≠1 (comp {X = 0F} {Y = 1F} 0F)
