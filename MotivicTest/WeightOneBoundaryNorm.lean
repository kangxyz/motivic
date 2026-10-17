/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneBoundaryNorm
public import Lean.Util.CollectAxioms

/-!
# Actual one-simplex support and fiber-norm consumers

The source is the literal simplex, its global algebra and projection are
proved finite/free/flat, and the fibers retain their whole scheme structure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.WeightOneBoundaryNorm Motivic.PresheafWithTransfers
open scoped Polynomial

universe u

namespace MotivicTest.WeightOneBoundaryNorm

variable {k : Type u} [Field k]

/-- Raw singular degree zero is identified with the actual base object. -/
def actual_degree_zero : Cor.simplexProduct (WeightOnePointNorm.point k) 0 ≅
    WeightOnePointNorm.point k := zeroProductIso k

/-- The selected actual first barycentric coordinate is the polynomial parameter. -/
theorem simplex_coordinate :
    oneCoordinateEquiv k (AlgebraicSimplex.coordinate k 1 0) = Polynomial.X :=
  oneCoordinateEquiv_coordinate_zero k

/-- Face zero is the zero fiber for this choice of parameter. -/
theorem actual_face_zero : facePoint k 0 = evaluationPoint k 0 := facePoint_zero k

/-- Face one is the one fiber for the same choice of parameter. -/
theorem actual_face_one : facePoint k 1 = evaluationPoint k 1 := facePoint_one k

/-- No flatness assumption is added to an arbitrary actual integral support. -/
theorem actual_projection_flat (Z : Generator k) : Flat Z.projection := inferInstance

/-- Finite generation is derived from the actual finite projection. -/
theorem actual_support_finite (Z : Generator k) : Module.Finite k[X] (coordinateRing Z) :=
  inferInstance

/-- Torsion-freeness is derived from integral support and surjectivity over the simplex. -/
theorem actual_support_torsionFree (Z : Generator k) :
    Module.IsTorsionFree k[X] (coordinateRing Z) := inferInstance

/-- The actual finite torsion-free algebra is free over the polynomial PID. -/
theorem actual_support_free (Z : Generator k) : Module.Free k[X] (coordinateRing Z) :=
  inferInstance

/-- The whole geometric fiber is identified with the tensor fiber as a base-field algebra. -/
def actual_fiber_algebra (Z : Generator k) (a : k) : Γ(fiber Z a, ⊤) ≃ₐ[k]
    Algebra.PolynomialFiber.Fiber (coordinateRing Z) a := fiberGlobalAlgEquiv Z a

/-- This identification preserves the literal Laurent coordinate. -/
theorem actual_fiber_coordinate (Z : Generator k) (a : k) :
    fiberGlobalEquiv Z a (fiberCoordinateUnit Z a : Γ(fiber Z a, ⊤)) =
      Algebra.PolynomialFiber.specialize (coordinateRing Z) a
        (coordinateUnit Z : coordinateRing Z) :=
  fiberGlobalEquiv_coordinate Z a

/-- Full endpoint scheme norms are equal without a reducedness or separability assumption. -/
theorem actual_endpoint_norms (Z : Generator k) :
    Units.map (Algebra.norm k) (fiberCoordinateUnit Z 0) =
      Units.map (Algebra.norm k) (fiberCoordinateUnit Z 1) :=
  geometric_fiber_unitNorm_eq Z 0 1

/-- The whole endpoint fiber is genuinely a closed subscheme of the target product. -/
theorem actual_endpoint_closed (Z : Generator k) (a : k) :
    IsClosedImmersion (fiberInclusion Z a) := inferInstance

/-- The actual reduced singular degree-zero norm retains its original point-cycle formula. -/
theorem actual_degree_zero_quotient
    (α : Cor.simplexProduct (WeightOnePointNorm.point k) 0 ⟶ WeightOnePointNorm.target k) :
    degreeZeroNorm k ((toReducedTorus k 1).hom.app
      (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0)) (ULift.up α)) =
        WeightOnePointNorm.cycleNorm k ((zeroProductIso k).inv ≫ α) :=
  degreeZeroNorm_quotient k α

/-- Every signed cycle has the same two actual endpoint norms. -/
theorem all_signed_endpoint_norms
    (α : Cor.mk (AlgebraicSimplex.smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k) :
    WeightOnePointNorm.cycleNorm k ((Cor.graphFunctor k).map (evaluationPoint k 0) ≫ α) =
      WeightOnePointNorm.cycleNorm k ((Cor.graphFunctor k).map (evaluationPoint k 1) ≫ α) :=
  cycleNorm_endpoint_eq α 0 1

/-- Every actual degree-one singular boundary dies in the actual reduced degree-zero norm. -/
theorem all_singular_boundaries
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (WeightOnePointNorm.point k) 1)) :
    degreeZeroNorm k
      ((singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 s) = 0 :=
  degreeZeroNorm_boundary k s

/-- Negating the actual differential does not invert the chosen degree-zero norm. -/
theorem shifted_negative_boundaries
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (WeightOnePointNorm.point k) 1)) :
    degreeZeroNorm k
      (-((singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 s)) = 0 :=
  degreeZeroNorm_negative_boundary k s

/-- The actual canonical shifted differential is negated before the norm is applied. -/
theorem canonical_raw_differential :
    (motivicRawBaseComplex k 1).d 0 1 =
      -((motivicRawBaseComplexXIso k 1 1).hom ≫
        (singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 ≫
          (motivicRawBaseComplexXIso k 1 0).inv) :=
  raw_d_zero_one k

/-- All boundaries in the actual canonical raw complex have zero norm. -/
theorem canonical_raw_boundaries (s : (motivicRawBaseComplex k 1).X 0) :
    rawDegreeZeroNorm k ((motivicRawBaseComplex k 1).d 0 1 s) = 0 :=
  rawDegreeZeroNorm_boundary k s

/-- The actual raw graph generator still has value a, with no inverse. -/
theorem canonical_raw_graph (a : kˣ) :
    rawDegreeZeroNorm k ((motivicRawBaseComplexXIso k 1 0).inv
      ((toReducedTorus k 1).hom.app
        (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0))
        (ULift.up ((zeroProductIso k).hom ≫
          (Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k a))))) =
      Additive.ofMul a :=
  rawDegreeZeroNorm_graph_unit k a

end MotivicTest.WeightOneBoundaryNorm

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOneBoundaryNorm.zeroSimplexIso,
      `Motivic.WeightOneBoundaryNorm.baseProductIso,
      `Motivic.WeightOneBoundaryNorm.zeroProductIso,
      `Motivic.WeightOneBoundaryNorm.oneSchemeIso,
      `Motivic.WeightOneBoundaryNorm.facePoint_zero,
      `Motivic.WeightOneBoundaryNorm.facePoint_one,
      `Motivic.WeightOneBoundaryNorm.scalarMap_injective,
      `Motivic.WeightOneBoundaryNorm.coordinateFinite,
      `Motivic.WeightOneBoundaryNorm.coordinateTorsionFree,
      `Motivic.WeightOneBoundaryNorm.coordinateFree,
      `Motivic.WeightOneBoundaryNorm.projectionFlat,
      `Motivic.WeightOneBoundaryNorm.fiberInclusionClosed,
      `Motivic.WeightOneBoundaryNorm.fiberSchemeIso,
      `Motivic.WeightOneBoundaryNorm.fiberGlobalAlgEquiv,
      `Motivic.WeightOneBoundaryNorm.fiberGlobalEquiv_restrict,
      `Motivic.WeightOneBoundaryNorm.fiberGlobalEquiv_coordinate,
      `Motivic.WeightOneBoundaryNorm.geometric_fiber_unitNorm_eq,
      `Motivic.WeightOneBoundaryNorm.degreeZeroNorm,
      `Motivic.WeightOneBoundaryNorm.degreeZeroNorm_quotient,
      `Motivic.WeightOneBoundaryNorm.degreeZeroNorm_face_quotient,
      `MotivicTest.WeightOneBoundaryNorm.actual_degree_zero,
      `MotivicTest.WeightOneBoundaryNorm.simplex_coordinate,
      `MotivicTest.WeightOneBoundaryNorm.actual_face_zero,
      `MotivicTest.WeightOneBoundaryNorm.actual_face_one,
      `MotivicTest.WeightOneBoundaryNorm.actual_projection_flat,
      `MotivicTest.WeightOneBoundaryNorm.actual_support_finite,
      `MotivicTest.WeightOneBoundaryNorm.actual_support_torsionFree,
      `MotivicTest.WeightOneBoundaryNorm.actual_support_free,
      `MotivicTest.WeightOneBoundaryNorm.actual_fiber_algebra,
      `MotivicTest.WeightOneBoundaryNorm.actual_fiber_coordinate,
      `MotivicTest.WeightOneBoundaryNorm.actual_endpoint_norms,
      `MotivicTest.WeightOneBoundaryNorm.actual_endpoint_closed,
      `MotivicTest.WeightOneBoundaryNorm.actual_degree_zero_quotient,
      `Motivic.WeightOneBoundaryNorm.cycleNorm_endpoint_generator,
      `Motivic.WeightOneBoundaryNorm.cycleNorm_endpoint_eq,
      `Motivic.WeightOneBoundaryNorm.degreeZeroNorm_boundary,
      `Motivic.WeightOneBoundaryNorm.degreeZeroNorm_negative_boundary,
      `MotivicTest.WeightOneBoundaryNorm.all_signed_endpoint_norms,
      `MotivicTest.WeightOneBoundaryNorm.all_singular_boundaries,
      `MotivicTest.WeightOneBoundaryNorm.shifted_negative_boundaries,
      `Motivic.WeightOneBoundaryNorm.rawDegreeZeroNorm,
      `Motivic.WeightOneBoundaryNorm.raw_d_zero_one,
      `Motivic.WeightOneBoundaryNorm.rawDegreeZeroNorm_boundary,
      `Motivic.WeightOneBoundaryNorm.rawDegreeZeroNorm_graph_unit,
      `MotivicTest.WeightOneBoundaryNorm.canonical_raw_differential,
      `MotivicTest.WeightOneBoundaryNorm.canonical_raw_boundaries,
      `MotivicTest.WeightOneBoundaryNorm.canonical_raw_graph] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual simplex support and fiber norms use only standard Lean foundations."
