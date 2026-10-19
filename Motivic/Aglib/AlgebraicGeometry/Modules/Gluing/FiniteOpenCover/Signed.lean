/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.FiniteOpenCover.Datum

/-!
# Signed finite descent data

A Boolean choice of local signs changes a genuine normalized descent datum
by nonidentity structure-sheaf-linear transitions and preserves its cocycle.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover

open Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

variable {X : Scheme.{u}} {ι : Type u}
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules)

/-- Actual open restriction preserves addition of module-sheaf morphisms. -/
instance restrictFunctor_additive {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] :
    (restrictFunctor f).Additive where
  map_add := rfl

/-- Negating both arrows gives an actual structure-sheaf-linear isomorphism. -/
def negatedIso {Y : Scheme.{u}} {P Q : Y.Modules} (e : P ≅ Q) : P ≅ Q where
  hom := -e.hom
  inv := -e.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- A change of local sign twists exactly the transitions between differently signed members. -/
def signedTransition (d : Datum U M) (s : ι → Bool) (i j : ι) : Transition U M i j :=
  if s i = s j then d.transition i j else negatedIso (d.transition i j)

set_option backward.isDefEq.respectTransparency false in
/-- Actual restriction carries the sign change to the same sign on the common-open transition. -/
theorem transitionOn_signed_hom (d : Datum U M) (s : ι → Bool) {W : X.Opens}
    (i j : ι) (hi : W ≤ U i) (hj : W ≤ U j) :
    (transitionOn U M (signedTransition U M d s) i j hi hj).hom =
      if s i = s j then (transitionOn U M d.transition i j hi hj).hom
      else -(transitionOn U M d.transition i j hi hj).hom := by
  by_cases h : s i = s j
  · simp only [transitionOn, signedTransition, h, ↓reduceIte]
  · simp only [transitionOn, signedTransition, h, ↓reduceIte, Iso.trans_hom,
      Functor.mapIso_hom, negatedIso, Functor.map_neg, Preadditive.comp_neg,
      Preadditive.neg_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Changing local signs preserves the ordinary normalized triple-overlap descent datum. -/
def signedDatum (d : Datum U M) (s : ι → Bool) : Datum U M where
  transition := signedTransition U M d s
  identity i := by simp [signedTransition, d.identity]
  cocycle W i j k hi hj hk := by
    apply Iso.ext
    have hc := congrArg Iso.hom (d.cocycle W i j k hi hj hk)
    simp only [Iso.trans_hom] at hc ⊢
    simp only [transitionOn_signed_hom]
    cases s i <;> cases s j <;> cases s k <;> simp [hc]

end AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
