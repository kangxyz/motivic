/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCoordinateCycleEvaluation
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual finite two-coordinate cycle evaluator

The source field is the entire given finite extension. No coordinate-generation,
separability, or source closed-immersion assumption is imposed. The consumers
retain original scalar maps, both units, geometric residue multiplicities, signed
coefficients, and collisions. Rational graphs normalize in the original Milnor
group. No boundary annihilation or homology descent is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.WeightTwoCoordinateEvaluation
open Motivic.WeightTwoCoordinateCycleEvaluation Motivic.WeightTwoCorestriction
open Motivic.WeightTwoPointPresentation

universe u

namespace MotivicTest.WeightTwoCoordinateCycleEvaluation

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
  (j : Spec (.of E) ⟶ ambient k) [IsFinite j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 2).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The image is used with the full original geometric residue degree. -/
theorem whole_fundamental_pushforward :
    FiniteCorrespondence.toIntegralCycle (finitePointCorrespondence j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E))) :=
  toIntegralCycle_finitePointCorrespondence j hj

/-- The literal image degree is the extension-to-image degree, with the original action. -/
theorem actual_image_degree (x : Spec (.of E)) :
    j.residueDegree x = Module.finrank (coordinateRing (imageGenerator j hj)) E :=
  residueDegree_eq_image_finrank j hj x

/-- Both structural maps are retained before any evaluation. -/
theorem original_scalar_tower :
    (imageScalarMap j hj).comp (algebraMap k (coordinateRing (imageGenerator j hj))) =
      algebraMap k E :=
  imageScalarMap_comp j hj

/-- Both original units are pulled back through the exact image-field map. -/
theorem original_coordinate_pullback (i : Fin 2) :
    Units.map (algebraMap (coordinateRing (imageGenerator j hj)) E).toMonoidHom
      (coordinateUnit (imageGenerator j hj) i) = affineCoordinateUnit j i :=
  imageScalarMap_coordinateUnit j hj i

include hj in
/-- An arbitrary actual representative is evaluated in the entire original point field. -/
theorem arbitrary_actual_representative
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleValue k α = value (k := k) (affineCoordinateUnit j 0) (affineCoordinateUnit j 1) :=
  cycleValue_eq_value_of_finite_fundamental j hj α hα

/-- Neither original coordinate is assumed to generate the full given extension. -/
theorem arbitrary_pair_evaluation (a b : Eˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E a b))) =
      value (k := k) a b :=
  cycleValue_pointPushforward_graph a b

/-- Base-valued coordinates still retain the degree of the entire extension. -/
theorem base_pair_retains_extension_degree [CharZero k] (a b : kˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E
        (Units.map (algebraMap k E).toMonoidHom a)
        (Units.map (algebraMap k E).toMonoidHom b)))) =
      Module.finrank k E • MilnorK.K2.symbol a b := by
  rw [cycleValue_pointPushforward_graph, value_map_degree, value_rational]

/-- Negative multiplicities and support collisions need no separate injectivity lemma. -/
theorem signed_colliding_pair_sum {ι : Type*} (s : Finset ι)
    (a b : ι → Eˣ) (n : ι → ℤ) :
    cycleValue k (∑ i ∈ s, n i • pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E (a i) (b i)))) =
      ∑ i ∈ s, n i • value (k := k) (a i) (b i) :=
  cycleValue_sum_pointPushforward_graph s a b n

/-- First identity-coordinate point cycles vanish in the original Milnor group. -/
theorem first_identity_axis (b : Eˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E 1 b))) = 0 :=
  cycleValue_pointPushforward_graph_one_left b

/-- Second identity-coordinate point cycles vanish in the original Milnor group. -/
theorem second_identity_axis (a : Eˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E a 1))) = 0 :=
  cycleValue_pointPushforward_graph_one_right a

/-- Normalization uses the actual rational graph, with no prospective comparison inverse. -/
theorem rational_graph_normalization [CharZero k] (a b : kˣ) :
    cycleValue k ((Cor.graphFunctor k).map (WeightTwoSymbols.rationalPair k a b)) =
      MilnorK.K2.symbol a b :=
  cycleValue_graph a b

/-- The identity-axis statement holds for arbitrary original signed supports. -/
theorem signed_identity_supports
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k)
    (hα : ∀ Z ∈ α.support, coordinateUnit Z 0 = 1 ∨ coordinateUnit Z 1 = 1) :
    cycleValue k α = 0 :=
  cycleValue_eq_zero_of_identity_support α hα

end MotivicTest.WeightTwoCoordinateCycleEvaluation

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightTwoCoordinateCycleEvaluation.ambient,
      `Motivic.WeightTwoCoordinateCycleEvaluation.ambientCoordinate,
      `Motivic.WeightTwoCoordinateCycleEvaluation.affineCoordinateUnit,
      `Motivic.WeightTwoCoordinateCycleEvaluation.affineCoordinateUnit_of_unitMap,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageGenerator,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageGenerator_toImage_projection,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageGenerator_support,
      `Motivic.WeightTwoCoordinateCycleEvaluation.finitePointCorrespondence,
      `Motivic.WeightTwoCoordinateCycleEvaluation.toIntegralCycle_finitePointCorrespondence,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageScalarMap,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageAlgebra,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageScalarMap_comp,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageScalarTower,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageScalarMap_coordinate,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageFinite,
      `Motivic.WeightTwoCoordinateCycleEvaluation.toImage_isoSpec,
      `Motivic.WeightTwoCoordinateCycleEvaluation.residueDegree_eq_image_finrank,
      `Motivic.WeightTwoCoordinateCycleEvaluation.imageScalarMap_coordinateUnit,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_finitePointCorrespondence,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_eq_value_of_finite_fundamental,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_eq_value_units_of_finite_fundamental,
      `Motivic.WeightTwoCoordinateCycleEvaluation.affineCoordinateUnit_scalarPoint_left,
      `Motivic.WeightTwoCoordinateCycleEvaluation.affineCoordinateUnit_scalarPoint_right,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_pointPushforward_graph,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_zsmul_pointPushforward_graph,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_sum_pointPushforward_graph,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_pointPushforward_graph_one_left,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_pointPushforward_graph_one_right,
      `Motivic.WeightTwoCoordinateCycleEvaluation.affineCoordinateUnit_graph_left,
      `Motivic.WeightTwoCoordinateCycleEvaluation.affineCoordinateUnit_graph_right,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_graph,
      `Motivic.WeightTwoCoordinateCycleEvaluation.cycleValue_eq_zero_of_identity_support,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.whole_fundamental_pushforward,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.actual_image_degree,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.original_scalar_tower,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.original_coordinate_pullback,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.arbitrary_actual_representative,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.arbitrary_pair_evaluation,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.base_pair_retains_extension_degree,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.signed_colliding_pair_sum,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.first_identity_axis,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.second_identity_axis,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.rational_graph_normalization,
      `MotivicTest.WeightTwoCoordinateCycleEvaluation.signed_identity_supports] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite two-coordinate cycles use only standard Lean foundations."
