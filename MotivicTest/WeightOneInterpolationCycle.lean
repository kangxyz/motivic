/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.InterpolationCycle

/-!
# Consumers of the actual whole monic interpolation correspondence

These tests use the genuine simplex, canonical torus power, original quotient
scheme, and length-weighted finite correspondences. No geometric integrality
or separability hypothesis is added to the whole family or its fibers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Polynomial.MonicUnitInterpolation
open Motivic.WeightOneInterpolationCycle

universe u

namespace Motivic.MotivicTest.WeightOneInterpolationCycle
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The actual whole quotient is a finite-flat closed correspondence support. -/
theorem whole_family_geometry (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    IsFinite (projection p) ∧ Flat (projection p) ∧ IsClosedImmersion (inclusion p hd h0) :=
  ⟨projection_finite hp hd, projection_flat hp hd, inclusion_closed hp hd h0⟩

/-- The signed correspondence uses exactly the full original fundamental cycle. -/
theorem whole_family_cycle (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    letI := inclusion_closed hp hd h0
    FiniteCorrespondence.toIntegralCycle (fundamentalCorrespondence hp hd h0) =
      IntegralCycle.finitePushforward (inclusion p hd h0) (fundamentalCycle (familyScheme p)) :=
  toIntegralCycle_fundamentalCorrespondence hp hd h0

/-- The actual zero-fiber scheme is the entire original quotient. -/
def whole_zero_fiber_iso (p : k[X]) : fiber p 0 ≅ Spec (.of (AdjoinRoot p)) :=
  fiberPolynomialSchemeIso p 0 p (fiberZeroEquiv p)

/-- The actual one-fiber scheme keeps the complete repeated-factor quotient. -/
def whole_one_fiber_iso (p : k[X]) : fiber p 1 ≅ Spec (.of (AdjoinRoot (target p))) :=
  fiberPolynomialSchemeIso p 1 (target p) (fiberOneEquiv p)

/-- Every original local multiplicity is retained in the zero endpoint. -/
theorem whole_zero_endpoint (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    letI := fiber_noetherian hp hd 0
    letI := fiberInclusion_closed hp hd h0 0
    IntegralCycle.finitePushforward (fiberInclusion p hd h0 0) (fundamentalCycle (fiber p 0)) =
      FiniteCorrespondence.toIntegralCycle (polynomialCycle p hp h0) :=
  zero_fiber_fundamental hp hd h0

/-- Every original local multiplicity is retained in the split endpoint. -/
theorem whole_one_endpoint (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    letI := fiber_noetherian hp hd 1
    letI := fiberInclusion_closed hp hd h0 1
    IntegralCycle.finitePushforward (fiberInclusion p hd h0 1) (fundamentalCycle (fiber p 1)) =
      FiniteCorrespondence.toIntegralCycle (polynomialCycle (target p) (target_monic p)
        ((target_coeff_zero p hd).trans_ne h0)) :=
  one_fiber_fundamental hp hd h0

/-- The actual signed correspondence-category endpoints are the two full polynomial cycles. -/
theorem actual_graph_restrictions (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k 0) ≫
        fundamentalCorrespondence hp hd h0 = polynomialCycle p hp h0) ∧
      ((Cor.graphFunctor k).map (WeightOneBoundaryNorm.evaluationPoint k 1) ≫
        fundamentalCorrespondence hp hd h0 =
          polynomialCycle (target p) (target_monic p) ((target_coeff_zero p hd).trans_ne h0)) :=
  ⟨graph_zero_fundamentalCorrespondence hp hd h0,
    graph_one_fundamentalCorrespondence hp hd h0⟩

/-- The genuine singular product convention has the same ordered cofaces. -/
theorem actual_singular_cofaces (p : k[X]) (hp : p.Monic)
    (hd : 1 ≤ p.natDegree) (h0 : p.coeff 0 ≠ 0) :
    ((WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          singularCorrespondence hp hd h0 = polynomialCycle p hp h0) ∧
      ((WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          singularCorrespondence hp hd h0 =
            polynomialCycle (target p) (target_monic p) ((target_coeff_zero p hd).trans_ne h0)) :=
  ⟨singularCorrespondence_face_zero hp hd h0, singularCorrespondence_face_one hp hd h0⟩

open Lean in
run_cmd do
  for name in #[``affineProjection, ``projection, ``projection_oneSchemeIso,
      ``projection_finite, ``projection_flat, ``constantMap, ``torusMap, ``targetMap,
      ``targetMap_coordinate, ``projection_structure, ``projection_base, ``inclusion,
      ``inclusion_fst, ``inclusion_snd, ``inclusion_finite, ``affinePullback,
      ``affinePullback_comp, ``family_hom_ext, ``inclusion_closed,
      ``component_projection_surjective, ``componentGenerator,
      ``componentGenerator_toIntegralClosedSubscheme, ``fundamentalCorrespondence,
      ``toIntegralCycle_fundamentalCorrespondence, ``polynomialUnit, ``polynomialUnit_val,
      ``polynomialTorusMap, ``polynomialTorusMap_closed, ``polynomialTargetMap,
      ``polynomialTargetMap_coordinate, ``polynomialTargetMap_structure,
      ``polynomialInclusion, ``polynomialInclusion_fst, ``polynomialInclusion_snd,
      ``polynomialInclusion_closed, ``polynomialCycle, ``toIntegralCycle_polynomialCycle,
      ``fiberSchemeIso, ``fiberSchemeIso_inv_fst, ``fiberSchemeIso_inv_snd,
      ``fiberInclusion, ``fiberInclusion_fst, ``fiberInclusion_snd,
      ``fiberProjection_finite, ``fiber_noetherian, ``fiberInclusion_closed,
      ``laurentRingHom_ext, ``specialize_constant, ``fiberPolynomialSchemeIso,
      ``fiberPolynomialSchemeIso_inv_fst, ``fiberPolynomialSchemeIso_inv_torus,
      ``fiberPolynomialSchemeIso_inv_inclusion, ``fiber_fundamental_eq_polynomialCycle,
      ``zero_fiber_fundamental, ``one_fiber_fundamental, ``componentSchemeIso,
      ``componentSchemeIso_hom_projection, ``componentSchemeIso_hom_target,
      ``componentFiberInclusion, ``componentFiberInclusion_closed, ``componentFiberIso,
      ``componentFiberIso_hom_inclusion, ``component_graph_restriction,
      ``fundamentalCorrespondence_graph_restriction_sum, ``fiberAffineIso,
      ``componentFiberAffineIso, ``affineComponentFiberInclusion,
      ``affineComponentFiberInclusion_closed, ``componentFiberAffineIso_hom_inclusion,
      ``fiber_fundamental_eq_component_sum, ``toIntegralCycle_graph_restriction,
      ``graph_zero_fundamentalCorrespondence, ``graph_one_fundamentalCorrespondence,
      ``face_zero_fundamentalCorrespondence, ``face_one_fundamentalCorrespondence,
      ``singularCorrespondence, ``singularCorrespondence_face,
      ``singularCorrespondence_face_zero, ``singularCorrespondence_face_one,
      ``actual_graph_restrictions, ``actual_singular_cofaces,
      ``whole_family_geometry, ``whole_family_cycle, ``whole_zero_fiber_iso,
      ``whole_one_fiber_iso, ``whole_zero_endpoint, ``whole_one_endpoint] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole monic interpolation geometry audit passed: standard foundations only."

end Motivic.MotivicTest.WeightOneInterpolationCycle
