{-# OPTIONS --safe --without-K #-}

-- The category with 2 objects and one morphism between them.
open import Interval

-- The category with 1 object and a non-trivial idempotent endomorphism.
open import NonTrivialEndo

-- Helper for reasoning about categories.
open import Reason

-- In MLTT, if one cannot eliminate reflexive endomorphisms for all families P : A -> Set, then A is a set.
open import Dinaturals.BijectionRefl

-- A result by Freyd: if all Set-valued dinaturals from a category C compose (pointwise), then C is a groupoid.
open import Dinaturals.ComposeGroupoid

-- hom is a monoid object, and there is a monad in the category of dipresheaves and dinaturals.
open import Dinaturals.CompositionMonad

-- Various results about dinaturals, including properties of products and pointwise implications.
open import Dinaturals.Dinaturals

-- The even-fixpoints dinaturals, determining whether a certain endomorphism has even or odd fixpoints; we show it cannot be composed with refl.
open import Dinaturals.EvenFixpoints

-- An example of loop-composition used to derive the (app) rule of simply-typed λ-calculus.
open import Dinaturals.ImplicationExample

-- Various helpers to state that the pointwise composition of two dinaturals is again dinatural.
open import Dinaturals.IsDinatural

-- Composition up-to loops and loop-composition, with the co/contra/two-sided flavours.
open import Dinaturals.LoopComposition

-- We show that using covariant and contravariant loop-compositions to compose with refl returns the original dinatural.
open import Dinaturals.LoopCompositionWithRefl

-- We encode a combinatorial example of two dinaturals not composing, using NonTrivialEndo.
open import Dinaturals.NonCompositionalityExample

-- We encode a combinatorial example of two dinaturals not composing, using instead NonTrivialEndo as a subcategory of Sets.
open import Dinaturals.NonCompositionalityExampleSet
