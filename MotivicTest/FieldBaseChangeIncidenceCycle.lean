/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.IncidenceCycle

/-!
# Whole incidence-cycle field-change checks

The field map is arbitrary and the coefficients are arbitrary integers. Neither
effectiveness, integrality of the new supports, nor separability is required.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition
open scoped BigOperators

universe u

namespace MotivicTest.FieldBaseChangeIncidenceCycle
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

example : IsFinite (A.fieldBaseChangeIncidenceMap φ B) := inferInstance

/-- The signed whole cycle is the sum of every original component's unreduced pullback. -/
theorem actualOriginalComponentPartition (c : genericPoints (A.incidence B) → ℤ) :
    IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
      (fun w => c (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
        A.fieldBaseChangeIncidenceFiberMultiplicity φ B w) =
    letI := IntegralCycle.genericPointFintype (A.incidence B)
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidencePullbackIso φ B).inv
      (∑ x : genericPoints (A.incidence B), c x •
        IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x)
          (fundamentalCycle (componentExterior (A.incidenceSource B ≫ X.hom)
            (Spec.map (CommRingCat.ofHom φ)) x))) :=
  A.fieldBaseChangeIncidenceCycle_eq_component_sum φ B c

open Lean in
run_cmd do
  for name in #[``actualOriginalComponentPartition,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidenceMap_isFinite,
      ``FiniteCorrespondenceGenerator.fieldBaseChangeIncidenceProjectionStalkArrowIso] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole incidence-cycle field change uses only standard foundations."

end MotivicTest.FieldBaseChangeIncidenceCycle
