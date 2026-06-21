{-# OPTIONS --safe --without-K #-}

open import Level
open import Relation.Nullary.Decidable using (Dec)

{-
  We formalize the dinatural transformation of even fixpoints from Bainbridge et al., which
  determines whether a certain endomorphism has an even or odd number of fixpoints.

  We assume the law of excluded middle for the above map.

  We explicitly show that this dinatural cannot be composed with the refl dinatural, in particular
  by instantiating the composition with the unique map from the BoolSetoid to the terminal setoid.
-}
module Dinaturals.EvenFixpoints
    (let
       ExplicitExcludedMiddle : (ℓ : Level) → Set (suc ℓ)
       ExplicitExcludedMiddle ℓ = (P : Set ℓ) → Dec P)
    (LEM : ∀ {ℓ} → ExplicitExcludedMiddle ℓ) where

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
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; ∃; ∃-syntax; proj₁; proj₂; _×_; Σ)
open import Data.Unit using (⊤; tt)
open import Function using () renaming (id to idf; _∘_ to _⟨∘⟩_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition renaming (function to _∘′_)
open import Function.Construct.Identity renaming (function to idS)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary.Decidable using (isYes; yes; no)
open import Data.Nat using (ℕ; _*_; _+_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (0↔⊥)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality
  using (cong; _≡_) renaming (refl to ≡-refl; trans to ≡-trans)
open import Relation.Nullary.Negation using (¬_)

open Functor using (F₀; F₁; homomorphism; F-resp-≈)
open Category using (op)

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as RS

open import Dinaturals.IsDinatural

import Reason

private
  variable
    o ℓ e : Level
    A B C Γ Δ Γ′ Γ″ Γᵒᵖ Δᵒᵖ : Category o ℓ e

private
  variable
    F G I J L : Functor (Product (op Γᵒᵖ) Γ) (Setoids ℓ ℓ)

private
  module Set {ℓ} = CartesianClosed (Setoids-CCC ℓ)
  module SetC {ℓ} = Cartesian (Set.cartesian {ℓ})
  module SetA {ℓ} = BinaryProducts (SetC.products {ℓ})
  module SetT {ℓ} = Terminal (SetC.terminal {ℓ})
  module F-⊤ {o} {ℓ} {e} = Terminal (One-⊤ {o} {ℓ} {e})

open import Relation.Binary.PropositionalEquality.Properties renaming (setoid to discreteSetoid)

-- Bool as a setoid.
BoolSetoid : Setoid zeroℓ zeroℓ
BoolSetoid = discreteSetoid Bool

-- Fin n as a setoid.
FinSetoid : ℕ → Setoid zeroℓ zeroℓ
FinSetoid n = discreteSetoid (Fin n)

-- The terminal setoid.
⊤Setoid : Setoid zeroℓ zeroℓ
⊤Setoid = discreteSetoid ⊤

-- The setoid of fixpoints for an endomorphism f : X → X.
Fixpoints : ∀ {ℓ} {X : Setoid ℓ ℓ} (f : Func X X) → Setoid ℓ ℓ
Fixpoints {X = X} f =
  let open Setoid X in
  record
    { Carrier = ∃[ x ] f ⟨$⟩ x ≈ x
    ; _≈_ = λ { x y → proj₁ x ≈ proj₁ y }
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }

record SetoidEquivalence {ℓ ℓ′} (A : Setoid ℓ ℓ) (B : Setoid ℓ′ ℓ′) : Set (ℓ ⊔ ℓ′) where
  private
    module A = Setoid A
    module B = Setoid B
  field
    to      : Func A B
    from    : Func B A
    to-from : ∀ x → from ⟨$⟩ (to ⟨$⟩ x) A.≈ x
    from-to : ∀ y → to ⟨$⟩ (from ⟨$⟩ y) B.≈ y

-- The from map in a setoid equivalence is injective.
SetoidEquivalence-from-injective :
  ∀ {ℓ ℓ′} {A : Setoid ℓ ℓ} {B : Setoid ℓ′ ℓ′}
  → (eq : SetoidEquivalence A B)
  → (let module eq = SetoidEquivalence eq)
  → (let module A = Setoid A)
  → (let module B = Setoid B)
  → {x : B.Carrier} {y : B.Carrier}
  → eq.from ⟨$⟩ x A.≈ eq.from ⟨$⟩ y
  → x B.≈ y
SetoidEquivalence-from-injective {A = A} {B = B} eq r = B.trans (B.sym (eq.from-to _)) (B.trans (Func.cong eq.to r) (eq.from-to _))
  where
    module eq = SetoidEquivalence eq
    module A = Setoid A
    module B = Setoid B

-- An addition map with better definitional equalities: namely that suc n + suc m = suc suc (n + m).
two-sided-add : ℕ → ℕ → ℕ
two-sided-add ℕ.zero ℕ.zero = ℕ.zero
two-sided-add ℕ.zero n = n
two-sided-add n ℕ.zero = n
two-sided-add (ℕ.suc m) (ℕ.suc n) = ℕ.suc (ℕ.suc (m + n))

-- The predicate stating that a setoid has an even number of elements, by giving an equivalence to a FinSetoid of the form Fin (2n).
HasEvenCardinality : ∀ {ℓ} (X : Setoid ℓ ℓ) → Set ℓ
HasEvenCardinality X =
  ∃[ n ] SetoidEquivalence X (FinSetoid (two-sided-add n n))

-- The key lemma: if f ∘ x has an even number of fixpoints, then x ∘ f has an even number of fixpoints.
even-cardinality-commute : ∀ {X Y : Setoid ℓ ℓ} (x : Func X Y) (f : Func Y X)
  → HasEvenCardinality (Fixpoints (f ∘′ x))
  → HasEvenCardinality (Fixpoints (x ∘′ f))
even-cardinality-commute {X = X} {Y} x f (n , eq) =
  let module X = Setoid X
      module Y = Setoid Y
      module eq = SetoidEquivalence eq in
  n , record
    { to = record { to = λ
      { (v , e) → eq.to ⟨$⟩ (x ⟨$⟩ v , Func.cong x e) }
      ; cong = λ r → Func.cong eq.to (Func.cong x r)
      }
    ; from = record
      { to = λ n →
        f ⟨$⟩ (proj₁ (eq.from ⟨$⟩ n)) , Func.cong f (proj₂ (eq.from ⟨$⟩ n))
      ; cong = λ { ≡-refl → X.refl }
      }
    ; to-from = λ { (v , p) → X.trans (Func.cong f (eq.to-from _)) p }
    ; from-to = λ { n → ≡-trans (Func.cong eq.to (proj₂ (eq.from ⟨$⟩ n))) (eq.from-to n) }
    }

-- Auxiliary lemmas showing that isYes respect logical equivalence of propositions (and viceversa) regardless of the decision procedures.
isYes-resp-⇔ : ∀ {P Q : Set ℓ} {z : Dec P} {z′ : Dec Q} (f : P → Q) (g : Q → P) → isYes z ≡ isYes z′
isYes-resp-⇔ {z = no p}  {z′ = no p′}  f g = ≡-refl
isYes-resp-⇔ {z = no p}  {z′ = yes p′} f g = ⊥-elim (p (g p′))
isYes-resp-⇔ {z = yes p} {z′ = no p′}  f g = ⊥-elim (p′ (f p))
isYes-resp-⇔ {z = yes p} {z′ = yes p′} f g = ≡-refl

isYes-≡-to-⇔ : ∀ {P Q : Set ℓ} {z : Dec P} {z′ : Dec Q} → isYes z ≡ isYes z′ → (P → Q) × (Q → P)
isYes-≡-to-⇔ {z = no p}  {z′ = no p′}  eq = (λ x → ⊥-elim (p x)) , (λ y → ⊥-elim (p′ y))
isYes-≡-to-⇔ {z = no p}  {z′ = yes p′} ()
isYes-≡-to-⇔ {z = yes p} {z′ = no p′}  ()
isYes-≡-to-⇔ {z = yes p} {z′ = yes p′} eq = (λ _ → p′) , (λ x → p)

-- There is a transport map between the fixpoints of two endomorphisms that are pointwise equal.
Fixpoints-transp : ∀ {X : Setoid ℓ ℓ} (f f′ : Func X X)
  (let module X = Setoid X)
  → (∀ {v} → f′ ⟨$⟩ v X.≈ f ⟨$⟩ v)
  → Func (Fixpoints f) (Fixpoints f′)
Fixpoints-transp {X = X} _ _ p =
  let open Setoid X in record
  { to = λ { (n , z) → n , trans p z }
  ; cong = λ x → x
  }

-- There is a transport map for the HasEvenCardinality setoid when two endomorphisms that are pointwise equal.
HasEvenCardinality-resp-≈ : ∀ {X : Setoid ℓ ℓ} (f f′ : Func X X)
  (let module X = Setoid X)
  → (∀ {v} → f′ ⟨$⟩ v X.≈ f ⟨$⟩ v)
  → HasEvenCardinality (Fixpoints f)
  → HasEvenCardinality (Fixpoints f′)
HasEvenCardinality-resp-≈ {X = X} f f′ p (n , eq) =
  let open Setoid X
      module eq = SetoidEquivalence eq in
  n , record
    { to = Fixpoints-transp f′ f (sym p) ∘′ eq.to
    ; from = eq.from ∘′ Fixpoints-transp f f′ p
    ; to-from = λ { (x , _) → eq.to-from _ }
    ; from-to = λ { n → ≡-trans (Func.cong eq.to refl) (eq.from-to n) }
    }

-- The even-fixpoints dinatural transformation, determining whether a certain endomorphism has even or odd fixpoints.
even-fixpoints : DinaturalTransformation Set.-⇨- (const BoolSetoid)
even-fixpoints = dtHelper record
  { α = λ X →
    let module X = Setoid X in record
    { to = λ x →
      -- Return the boolean value which LEM decides for the proposition "HasEvenCardinality (Fixpoints x)".
      isYes (LEM (HasEvenCardinality (Fixpoints x)))
    ; cong = λ { {f} {f′} e →
      isYes-resp-⇔ (HasEvenCardinality-resp-≈ f f′ (X.sym e)) (HasEvenCardinality-resp-≈ f′ f e)
    } }
  ; commute =
    λ f {x} → isYes-resp-⇔ (even-cardinality-commute x f) (even-cardinality-commute f x)
  }

-- Identity dinatural for Set.
id-Set : DinaturalTransformation (const ⊤Setoid) Set.-⇨-
id-Set = dtHelper record
  { α = λ X →
    let module X = Setoid X in record
    { to = λ x → idS X
    ; cong = λ _ → X.refl
    }
  ; commute = λ { {X} {Y} f → Setoid.refl Y }
  }

-- The unique map from the BoolSetoid to the terminal setoid.
func-Bool-⊤ : Func BoolSetoid ⊤Setoid
func-Bool-⊤ = record
  { to = λ x → tt
  ; cong = λ e → ≡-refl
  }

-- The identity function on Bool has an even number of fixpoints, i.e., 2.
fixpoints-id-bool-even :
  HasEvenCardinality (Fixpoints (idS BoolSetoid))
fixpoints-id-bool-even = 1 , record
  { to = record
    { to = λ { (false , _) → 0F
             ; (true , _) → 1F }
    ; cong = λ { {true  , _} ≡-refl → ≡-refl
               ; {false , _} ≡-refl → ≡-refl  } }
  ; from = record { to = λ { 0F → false , ≡-refl
                           ; 1F → true , ≡-refl }
                  ; cong = λ { {0F} ≡-refl → ≡-refl
                             ; {1F} ≡-refl → ≡-refl } }
  ; to-from = λ { (false , _) → ≡-refl
                ; (true , _) → ≡-refl }
  ; from-to = λ { 0F → ≡-refl
                ; 1F → ≡-refl }
  }

-- Auxiliary lemma showing that 1 is not equal to 0 in Fin (suc n).
0≠1 : ∀ {n} → ¬ (1F ≡ Fin.zero {n = ℕ.suc n}  )
0≠1 ()

-- The identity function on the terminal setoid has an odd number of fixpoints.
¬fixpoints-id-⊤-even :
  ¬ HasEvenCardinality (Fixpoints (idS ⊤Setoid))
¬fixpoints-id-⊤-even (ℕ.zero , eq) =
  let module eq = SetoidEquivalence eq in
    Function.Inverse.to 0↔⊥ (eq.to ⟨$⟩ (tt , ≡-refl))
¬fixpoints-id-⊤-even (ℕ.suc n , eq) =
  let module eq = SetoidEquivalence eq in
  0≠1 (SetoidEquivalence-from-injective eq {x = 1F} {y = 0F} ≡-refl)

-- Final result: the composition of the even-fixpoints dinatural with the identity dinatural for Set is not dinatural, since it depends on the set being picked.
noComposition : ¬ CompositionIsDinatural id-Set even-fixpoints
noComposition c =
  ¬fixpoints-id-⊤-even
    (proj₁ (isYes-≡-to-⇔ (c {X = BoolSetoid} {Y = ⊤Setoid} func-Bool-⊤ {x = tt}))
           fixpoints-id-bool-even)
