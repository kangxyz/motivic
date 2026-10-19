/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.PointNorm
public import Lean.Util.CollectAxioms

/-!
# Consumers of the norm on actual weight-one point cycles

These tests keep arbitrary fields, actual integral finite supports, signed
multiplicities, and the canonical one-fold product target and cokernel.
They do not assume separability, annihilation of singular boundaries, or a
motivic cohomology computation.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Opposite
open Motivic Motivic.WeightOnePointNorm _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.WeightOnePointNorm

variable {k : Type u} [Field k]

/-- A genuine support has an actual finite field coordinate ring. -/
theorem support_field (Z : Generator k) :
    IsField (coordinateRing Z) ∧ Module.Finite k (coordinateRing Z) :=
  ⟨coordinateRing_isField Z, inferInstance⟩

/-- The generator value is the existing determinant norm of the pulled-back Laurent unit. -/
theorem actual_norm (Z : Generator k) :
    (generatorNorm Z : k) = Algebra.norm k (coordinateUnit Z : coordinateRing Z) :=
  generatorNorm_val Z

/-- All signed coefficients are retained, including negative multiplicities. -/
theorem signed_multiplicity (Z : Generator k) (n : ℤ) :
    cycleNorm k (Finsupp.single Z n) = n • Additive.ofMul (generatorNorm Z) :=
  cycleNorm_single Z n

/-- Degree-zero graph normalization is the unit itself, rather than its inverse. -/
theorem graph_normalization (a : kˣ) :
    cycleNorm k ((Cor.graphFunctor k).map (rationalPoint k a)) = Additive.ofMul a :=
  cycleNorm_graph_unit a

/-- A negative actual graph has the reciprocal norm. -/
theorem negative_graph (a : kˣ) :
    cycleNorm k (-((Cor.graphFunctor k).map (rationalPoint k a))) =
      Additive.ofMul a⁻¹ := by
  exact (map_neg (cycleNorm k) ((Cor.graphFunctor k).map (rationalPoint k a))).trans
    (congrArg Neg.neg (cycleNorm_graph_unit a))

/-- Addition of actual cycles becomes multiplication of the field units. -/
theorem sum_of_graphs (a b : kˣ) :
    cycleNorm k ((Cor.graphFunctor k).map (rationalPoint k a) +
      (Cor.graphFunctor k).map (rationalPoint k b)) = Additive.ofMul (a * b) := by
  exact (map_add (cycleNorm k) ((Cor.graphFunctor k).map (rationalPoint k a))
    ((Cor.graphFunctor k).map (rationalPoint k b))).trans
      (congrArg₂ (· + ·) (cycleNorm_graph_unit a) (cycleNorm_graph_unit b))

/-- Every signed identity-axis image, using actual categorical composition, is killed. -/
theorem all_identity_axis_cycles (α : point k ⟶ point k) :
    cycleNorm k (α ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0)) = 0 :=
  cycleNorm_identityAxis α

/-- The actual reduced-torus quotient has the same graph normalization. -/
theorem canonical_quotient_graph (a : kˣ) :
    reducedNorm k ((toReducedTorus k 1).hom.app (op (point k))
      (ULift.up ((Cor.graphFunctor k).map (rationalPoint k a)))) = Additive.ofMul a :=
  reducedNorm_graph_unit a

/-- Arbitrary signed cycles retain the determinant norm after the canonical quotient. -/
theorem canonical_quotient_cycle (α : point k ⟶ target k) :
    reducedNorm k ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up α)) =
      cycleNorm k α :=
  reducedNorm_quotient α

/-- The actual quotient norm reaches every unit, without asserting injectivity. -/
theorem quotient_norm_surjective : Function.Surjective (reducedNorm k) :=
  reducedNorm_surjective

end MotivicTest.WeightOnePointNorm

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOnePointNorm.supportIsoSpec,
      `Motivic.WeightOnePointNorm.scalarMap,
      `Motivic.WeightOnePointNorm.coordinateFinite,
      `Motivic.WeightOnePointNorm.coordinateRing_isField,
      `Motivic.WeightOnePointNorm.coordinateUnit,
      `Motivic.WeightOnePointNorm.generatorNorm,
      `Motivic.WeightOnePointNorm.cycleNorm,
      `Motivic.WeightOnePointNorm.graph_finrank,
      `Motivic.WeightOnePointNorm.graph_coordinate,
      `Motivic.WeightOnePointNorm.generatorNorm_graph,
      `Motivic.WeightOnePointNorm.rationalPoint,
      `Motivic.WeightOnePointNorm.rationalCoordinate_rationalPoint,
      `Motivic.WeightOnePointNorm.cycleNorm_graph_unit,
      `Motivic.WeightOnePointNorm.cycleNorm_identityAxis,
      `Motivic.WeightOnePointNorm.reducedNorm,
      `Motivic.WeightOnePointNorm.reducedNorm_quotient,
      `Motivic.WeightOnePointNorm.reducedNorm_graph_unit,
      `Motivic.WeightOnePointNorm.reducedNorm_surjective,
      `MotivicTest.WeightOnePointNorm.support_field,
      `MotivicTest.WeightOnePointNorm.actual_norm,
      `MotivicTest.WeightOnePointNorm.signed_multiplicity,
      `MotivicTest.WeightOnePointNorm.graph_normalization,
      `MotivicTest.WeightOnePointNorm.negative_graph,
      `MotivicTest.WeightOnePointNorm.sum_of_graphs,
      `MotivicTest.WeightOnePointNorm.all_identity_axis_cycles,
      `MotivicTest.WeightOnePointNorm.canonical_quotient_graph,
      `MotivicTest.WeightOnePointNorm.canonical_quotient_cycle,
      `MotivicTest.WeightOnePointNorm.quotient_norm_surjective] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual point norms and quotient consumers use only standard Lean foundations."
