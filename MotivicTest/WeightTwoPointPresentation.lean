/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.PointPresentation
public import Lean.Util.CollectAxioms

/-!
# Original-generator consumers of the two-coordinate point presentation

The full support field, original degree, scalar map, and both units remain
visible. MotivicTest use the actual cycle group and raw and derived H22 groups;
all accepted declarations are checked against standard foundational axioms.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open WeightTwoPointPresentation WeightTwoCorestriction
open MilnorK.K3.PolynomialResidue

universe w u

namespace MotivicTest.WeightTwoPointPresentation

variable {k : Type u} [Field k] [CharZero k] (Z : Generator k)

local instance polynomialFinite (p : MonicIrreducible k) : Module.Finite k (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

/-- The primitive polynomial retains the full joint field's original degree. -/
theorem actual_joint_field_degree :
    (polynomial Z).val.natDegree = Module.finrank k (coordinateRing Z) :=
  polynomial_natDegree Z

/-- The original joint field is the entire literal polynomial quotient. -/
def actual_joint_field_equivalence : AdjoinRoot (polynomial Z).val ≃ₐ[k] coordinateRing Z :=
  rootEquiv Z

/-- The first coordinate survives as the original unit in the full support field. -/
theorem actual_first_unit :
    rootEquiv Z (WeightTwoPointPresentation.polynomialUnit Z 0 :
      AdjoinRoot (polynomial Z).val) = (coordinateUnit Z 0 : coordinateRing Z) :=
  rootEquiv_polynomialUnit Z 0

/-- The second coordinate survives in the same field and under the same quotient chart. -/
theorem actual_second_unit :
    rootEquiv Z (WeightTwoPointPresentation.polynomialUnit Z 1 :
      AdjoinRoot (polynomial Z).val) = (coordinateUnit Z 1 : coordinateRing Z) :=
  rootEquiv_polynomialUnit Z 1

/-- The actual scalar map is unchanged by the polynomial presentation. -/
theorem actual_scalar_map :
    (polynomialSupportIso Z).hom ≫ Z.projection =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of (polynomial Z).val)) :=
  polynomialSupportIso_projection Z

/-- The complete original closed immersion is the actual scalar rational pair. -/
theorem actual_closed_support :
    (polynomialSupportIso Z).hom ≫ Z.inclusion =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair (AdjoinRoot (polynomial Z).val)
        (WeightTwoPointPresentation.polynomialUnit Z 0)
        (WeightTwoPointPresentation.polynomialUnit Z 1)) :=
  polynomialSupportIso_inclusion Z

/-- The original generator has coefficient one and retains the whole polynomial field. -/
theorem actual_generator :
    ∃ (p : MonicIrreducible k) (a b : (AdjoinRoot p.val)ˣ),
      p.val.natDegree = Module.finrank k (coordinateRing Z) ∧
        Z.cycle = pointPushforward (k := k)
          ((Cor.graphFunctor (AdjoinRoot p.val)).map (WeightTwoSymbols.rationalPair _ a b)) :=
  exists_pointPushforward Z

/-- Positive and negative multiplicities are retained in the original cycle group. -/
theorem actual_signed_generator (n : ℤ) :
    n • Z.cycle = pointPushforward (k := k)
      (n • (Cor.graphFunctor (AdjoinRoot (polynomial Z).val)).map
        (WeightTwoSymbols.rationalPair _ (WeightTwoPointPresentation.polynomialUnit Z 0)
          (WeightTwoPointPresentation.polynomialUnit Z 1))) := by
  erw [map_zsmul, generator_cycle_eq_pointPushforward]

/-- An original raw H22 generator is the existing finite corestriction. -/
theorem actual_raw_generator :
    WeightTwoSymbols.cycleClass k Z.cycle =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
        (WeightTwoPointPresentation.polynomialUnit Z 0)
        (WeightTwoPointPresentation.polynomialUnit Z 1)) :=
  cycleClass_generator Z

/-- Every original raw class is a signed sum of the actual transferred graph symbols. -/
theorem actual_raw_class (x : (motivicRawBaseComplex k 2).homology 2) :
    ∃ α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k,
      x = α.sum (fun Z n => n • corestriction (k := k)
        (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
          (WeightTwoPointPresentation.polynomialUnit Z 0)
          (WeightTwoPointPresentation.polynomialUnit Z 1))) :=
  exists_sum_corestriction k x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The genuine derived comparison carries the same original generator equality. -/
theorem actual_derived_generator :
    (motivicRawBaseEvaluationComparison k 2 2).symm (WeightTwoSymbols.cycleClass k Z.cycle) =
      (motivicRawBaseEvaluationComparison k 2 2).symm
        (corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
          (WeightTwoPointPresentation.polynomialUnit Z 0)
          (WeightTwoPointPresentation.polynomialUnit Z 1))) :=
  congrArg _ (cycleClass_generator Z)

/-- Every element of the actual derived H22 group has the same finite-transfer presentation. -/
theorem actual_derived_class
    (x : motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) :
    ∃ α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k,
      motivicRawBaseEvaluationComparison k 2 2 x =
        α.sum (fun Z n => n • corestriction (k := k)
          (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
            (WeightTwoPointPresentation.polynomialUnit Z 0)
            (WeightTwoPointPresentation.polynomialUnit Z 1))) :=
  exists_sum_corestriction k (motivicRawBaseEvaluationComparison k 2 2 x)

open Lean in
run_cmd do
  for name in #[``coordinateRing_isField, ``coordinateField, ``coordinateFinite,
      ``coordinatePullback_eq_eval, ``primitiveElement, ``primitiveElement_generates,
      ``polynomial, ``polynomial_natDegree, ``rootEquiv, ``rootEquiv_polynomialUnit,
      ``polynomialSupportIso, ``polynomialSupportIso_projection,
      ``polynomialSupportIso_coordinate, ``polynomialSupportIso_inclusion,
      ``generator_cycle_eq_pointPushforward, ``cycleClass_generator, ``exists_pointPushforward,
      ``cycle_eq_sum_pointPushforward, ``cycleClass_eq_sum_corestriction,
      ``exists_sum_corestriction, ``actual_joint_field_degree, ``actual_joint_field_equivalence,
      ``actual_first_unit, ``actual_second_unit, ``actual_scalar_map, ``actual_closed_support,
      ``actual_generator, ``actual_signed_generator, ``actual_raw_generator,
      ``actual_raw_class, ``actual_derived_generator, ``actual_derived_class] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Exact whole-field weight-two point presentations use only standard foundations."

end MotivicTest.WeightTwoPointPresentation
