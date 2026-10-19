/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Cycle

/-!
# Consumers of actual signed field change

These tests use arbitrary field maps, without finite-type restrictions on the
extension, and allow disconnected smooth schemes. All multiplicities are the
original unreduced support lengths, and all signed coefficients are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped BigOperators

universe u

namespace MotivicTest.FieldBaseChangeCycle
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The operation is a genuine additive homomorphism on all signed correspondences. -/
def actualSignedMap : FiniteCorrespondence X.hom Y.hom →+
    FiniteCorrespondence ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom :=
  FiniteCorrespondence.fieldBaseChange φ

/-- The exact component sum keeps the whole-support length, including nilpotents. -/
theorem wholeSupportLengthSum : A.fieldBaseChangeCycle φ =
    letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    ∑ w, Finsupp.single (A.fieldBaseChangeComponentGenerator φ w)
      ((Module.length ((A.fieldBaseChangeSupport φ).presheaf.stalk w.1)
        ((A.fieldBaseChangeSupport φ).presheaf.stalk w.1)).toNat : ℤ) :=
  A.fieldBaseChangeCycle_eq_sum φ

/-- An arbitrary signed multiple has precisely the actual whole-support pushforward. -/
theorem exactSignedGeneratorFormula (n : ℤ) :
    FiniteCorrespondence.toIntegralCycle
      (actualSignedMap (X := X) (Y := Y) φ (Finsupp.single A n)) =
        n • IntegralCycle.finitePushforward (A.fieldBaseChangeInclusion φ)
          (fundamentalCycle (A.fieldBaseChangeSupport φ)) :=
  FiniteCorrespondence.toIntegralCycle_fieldBaseChange_single φ A n

/-- All original supports and their signed coefficients occur in the exact formula. -/
theorem exactWholeCycleFormula (α : FiniteCorrespondence X.hom Y.hom) :
    FiniteCorrespondence.toIntegralCycle (actualSignedMap (X := X) (Y := Y) φ α) =
      α.sum (fun B n => n • IntegralCycle.finitePushforward (B.fieldBaseChangeInclusion φ)
        (fundamentalCycle (B.fieldBaseChangeSupport φ))) :=
  FiniteCorrespondence.toIntegralCycle_fieldBaseChange φ α

/-- Opposite input coefficients cancel after actual field change. -/
theorem signedCancellation (α : FiniteCorrespondence X.hom Y.hom) :
    actualSignedMap (X := X) (Y := Y) φ (α + -α) = 0 := by
  rw [add_neg_cancel]
  exact map_zero _

/-- No arbitrary component is selected when the support is empty. -/
theorem emptySupport [IsEmpty (A.fieldBaseChangeSupport φ)] :
    A.fieldBaseChangeCycle φ = 0 := A.fieldBaseChangeCycle_of_isEmpty φ

/-- If the new source is empty, every signed correspondence has zero field change. -/
theorem emptyNewSource [IsEmpty ((SmoothSite.fieldBaseChange φ).obj X).left]
    (α : FiniteCorrespondence X.hom Y.hom) :
    actualSignedMap (X := X) (Y := Y) φ α = 0 := by
  ext B
  exact isEmptyElim (α := ((SmoothSite.fieldBaseChange φ).obj X).left)
    (B.projection (Classical.arbitrary B.scheme))

open Classical in
/-- Every coincident component image contributes its original integer coefficient. -/
theorem exactImageCollisionSum (c : genericPoints (A.fieldBaseChangeSupport φ) → ℤ)
    (B : FiniteCorrespondenceGenerator ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom) :
    A.fieldBaseChangeCycleAssembly φ c B =
      letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
      ∑ w, if A.fieldBaseChangeComponentGenerator φ w = B then c w else 0 :=
  A.fieldBaseChangeCycleAssembly_coefficient φ c B

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondenceGenerator.fieldBaseChangeCycleAssembly,
      ``FiniteCorrespondenceGenerator.toIntegralCycle_fieldBaseChangeCycleAssembly,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeCycle,
      ``FiniteCorrespondenceGenerator.toIntegralCycle_fieldBaseChangeCycle,
      ``FiniteCorrespondence.fieldBaseChange,
      ``FiniteCorrespondence.toIntegralCycle_fieldBaseChange,
      ``wholeSupportLengthSum, ``exactSignedGeneratorFormula, ``exactWholeCycleFormula,
      ``signedCancellation, ``emptySupport, ``emptyNewSource, ``exactImageCollisionSum] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual signed field-base-change cycles use only standard foundations."

end MotivicTest.FieldBaseChangeCycle
