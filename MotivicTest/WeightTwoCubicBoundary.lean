/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CubicBoundary
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual finite-flat cubic endpoint boundary

These tests keep the literal full polynomial quotients, both exact singular
faces, and the actual raw weight-two homology target. Characteristic three
and `a³+1=0` are included. No Steinberg or Milnor comparison is asserted.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Motivic
open Polynomial.TwoUnitPolynomialFamily Motivic.WeightTwoCubicBoundary

universe u

namespace MotivicTest.WeightTwoCubicBoundary

variable {k : Type u} [Field k]

/-- The whole cubic has a finite-flat surjective parameter projection. -/
theorem actual_projection (a : k) :
    IsFinite (projection (cubic a)) ∧ Flat (projection (cubic a)) ∧
      Function.Surjective (projection (cubic a)) :=
  ⟨projection_finite (cubic_monic a), projection_flat (cubic_monic a),
    projection_surjective (cubic_monic a) (by rw [cubic_natDegree]; decide)⟩

/-- The literal cubic image in the parameter-two-torus product is closed. -/
theorem actual_closed_image (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    IsClosedImmersion (inclusion (cubic a)
      (cubic_eval_zero_isUnit a ha) (cubic_eval_one_isUnit a ha3)) :=
  inclusion_closed (cubic_monic a) _ _

/-- Every original generic multiplicity survives assembly of the cubic correspondence. -/
theorem actual_whole_family (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    letI := actual_closed_image a ha ha3
    FiniteCorrespondence.toIntegralCycle
        (fundamentalCorrespondence (cubic a) (cubic_monic a)
          (cubic_eval_zero_isUnit a ha) (cubic_eval_one_isUnit a ha3)) =
      IntegralCycle.finitePushforward
        (inclusion (cubic a) (cubic_eval_zero_isUnit a ha) (cubic_eval_one_isUnit a ha3))
        (fundamentalCycle (familyScheme (cubic a))) :=
  toIntegralCycle_fundamentalCorrespondence _ _ _ _

/-- Both literal faces are the full specified polynomial quotient cycles. -/
theorem actual_faces (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    ((WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          cubicCorrespondence a ha ha3 = zeroCycle a ha ha3) ∧
      ((WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          cubicCorrespondence a ha ha3 = oneCycle a ha ha3) :=
  ⟨cubicCorrespondence_face_zero _ _ _, cubicCorrespondence_face_one _ _ _⟩

/-- The endpoint class equality is in the originally defined raw homology. -/
theorem actual_endpoint_classes (a : k) (ha : a ≠ 0) (ha3 : a ^ 3 ≠ 1) :
    WeightTwoSymbols.cycleClass k (zeroCycle a ha ha3) =
      WeightTwoSymbols.cycleClass k (oneCycle a ha ha3) :=
  cubic_cycleClass_endpoints _ _ _

/-- The shift used for this raw boundary has its actual positive sign. -/
theorem actual_positive_raw_sign :
    (motivicRawBaseComplex k 2).d 1 2 =
      (motivicRawBaseComplexXIso k 2 1).hom ≫
        (PresheafWithTransfers.singularObj (PresheafWithTransfers.reducedTorus k 2)
          (WeightOnePointNorm.point k)).d 1 0 ≫
          (motivicRawBaseComplexXIso k 2 0).inv :=
  WeightTwoSymbols.raw_d_one_two k

/-- Characteristic three with `a³+1=0` remains admissible, including all repeated roots. -/
theorem characteristic_three_endpoint_classes :
    WeightTwoSymbols.cycleClass (ZMod 3) (zeroCycle (2 : ZMod 3) (by decide) (by decide)) =
      WeightTwoSymbols.cycleClass (ZMod 3) (oneCycle (2 : ZMod 3) (by decide) (by decide)) :=
  cubic_cycleClass_endpoints _ _ _

/-- This test case violates the unnecessary graph-integrality nondegeneracy assumption. -/
theorem characteristic_three_degenerate_parameter : (2 : ZMod 3) ^ 3 + 1 = 0 := by decide

open Lean in
run_cmd do
  for name in #[``unitMap, ``unitMap_structure, ``pairMap, ``pairMap_first,
      ``pairMap_second, ``pairMap_structure, ``pair_hom_ext, ``unitMap_comp, ``pairMap_comp,
      ``projection, ``constantMap, ``targetMap, ``inclusion, ``inclusion_fst, ``inclusion_snd,
      ``projection_finite, ``projection_flat, ``family_hom_ext, ``inclusion_closed,
      ``projection_surjective, ``polynomialTargetMap, ``polynomialFirst_closed,
      ``polynomialInclusion, ``polynomialInclusion_closed, ``polynomialProjection_finite,
      ``polynomialCycle, ``toIntegralCycle_polynomialCycle, ``fundamentalCorrespondence,
      ``toIntegralCycle_fundamentalCorrespondence, ``fiberSchemeIso,
      ``fiberPolynomialSchemeIso, ``fiberPolynomialSchemeIso_inv_fst,
      ``fiberPolynomialSchemeIso_inv_snd, ``endpoint_targetMap,
      ``specialize_eval_zero_isUnit, ``specialize_eval_one_isUnit,
      ``fiberInclusion, ``fiberInclusion_closed, ``fiberPolynomialSchemeIso_inv_inclusion,
      ``fiber_fundamental_eq_polynomialCycle, ``graph_restriction, ``simplexLineMap,
      ``evaluationPoint_simplexLineMap, ``singularCorrespondence,
      ``singularCorrespondence_face_zero, ``singularCorrespondence_face_one,
      ``cycleClass_endpoints, ``cubicZero_monic, ``cubicOne_monic, ``zeroCycle, ``oneCycle,
      ``cubicCorrespondence, ``cubicCorrespondence_face_zero, ``cubicCorrespondence_face_one,
      ``cubic_cycleClass_endpoints, ``actual_projection, ``actual_closed_image,
      ``actual_whole_family, ``actual_faces, ``actual_endpoint_classes,
      ``actual_positive_raw_sign, ``characteristic_three_endpoint_classes,
      ``characteristic_three_degenerate_parameter] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual whole cubic endpoint cycles use only standard Lean foundations."

end MotivicTest.WeightTwoCubicBoundary
