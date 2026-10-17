/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCoordinateEvaluation
public import MotivicTest.PolynomialFiberNorm
public import Lean.Util.CollectAxioms

/-!
# Consumers of independent first-coordinate Milnor evaluation

The tests keep the whole original field when the first coordinate belongs to
a proper subfield, arbitrary signed support coefficients, and actual square-zero
polynomial fibers. They test a restricted Milnor-valued endpoint theorem, not an
inverse map on motivic homology or arbitrary norm presentation independence.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Motivic
open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK3.PolynomialResidue
open Motivic.KTheory.MilnorK3.PolynomialNorm
open Motivic.WeightTwoCoordinateEvaluation Algebra.PolynomialFiber

universe u

namespace MotivicTest.WeightTwoCoordinateEvaluation

variable {k E D : Type u} [Field k] [Field E] [Field D]
  [Algebra k E] [Module.Finite k E]

/-- The retained coefficient is the degree above the whole original point field. -/
theorem actual_field_degree [Algebra k D] [Algebra E D] [IsScalarTower k E D]
    [Module.Finite E D] [Module.Finite k D] (a b : Eˣ) :
    value (k := k) (Units.map (algebraMap E D).toMonoidHom a)
      (Units.map (algebraMap E D).toMonoidHom b) =
      Module.finrank E D • value (k := k) a b :=
  value_map_degree a b

/-- Neither identity-coordinate relation requires a descent hypothesis. -/
theorem actual_identity_axes (a b : Eˣ) :
    value (k := k) a 1 = 0 ∧ value (k := k) 1 b = 0 :=
  ⟨value_one_right a, value_one_left b⟩

/-- Original rational symbols are recovered inside the Milnor group itself. -/
theorem actual_rational [CharZero k] (a b : kˣ) : value (k := k) a b = symbol a b :=
  value_rational a b

/-- Signed original supports keep the same entire global-section field and units. -/
theorem actual_signed_support (Z : WeightTwoPointPresentation.Generator k) (n : ℤ) :
    cycleValue k (Finsupp.single Z n) = n • value (k := k)
      (WeightTwoPointPresentation.coordinateUnit Z 0)
      (WeightTwoPointPresentation.coordinateUnit Z 1) :=
  cycleValue_single Z n

variable (p : MonicIrreducible k) (hp0 : p.val.coeff 0 ≠ 0)

local instance finiteRoot : Module.Finite k (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

/-- The first coordinate has degree one while the joint field is genuinely
larger. The root second coordinate still contributes its whole ordinary norm. -/
theorem proper_first_coordinate [CharZero k] (hp : 1 < p.val.natDegree) (a : kˣ) :
    (firstPolynomial (k := k)
      (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a)).val.natDegree = 1 ∧
      1 < Module.finrank k (AdjoinRoot p.val) ∧
      value (k := k) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom a)
        (rootUnit p hp0) = symbol a (Units.map (Algebra.norm k) (rootUnit p hp0)) := by
  refine ⟨?_, ?_, value_base_first a (rootUnit p hp0)⟩
  · change (minpoly k (algebraMap k (AdjoinRoot p.val) (a : k))).natDegree = 1
    rw [minpoly.eq_X_sub_C, natDegree_X_sub_C]
  · have hd : Module.finrank k (AdjoinRoot p.val) = p.val.natDegree :=
      finrank_quotient_span_eq_natDegree
    rwa [hd]

/-- Every actual dual-number evaluation fiber contains a nonzero nilpotent. -/
theorem actual_nonreduced_fiber (a : AdjoinRoot p.val) :
    specialize (DualNumber (AdjoinRoot p.val)[X]) a DualNumber.eps ≠ 0 ∧
      specialize (DualNumber (AdjoinRoot p.val)[X]) a DualNumber.eps ^ 2 = 0 :=
  Motivic.MotivicTest.PolynomialFiberNorm.dualFiber_nonreduced a

local instance finiteDual :
    Module.Finite (AdjoinRoot p.val)[X] (DualNumber (AdjoinRoot p.val)[X]) :=
  Motivic.MotivicTest.PolynomialFiberNorm.dualPolynomial_finiteFree.1

local instance freeDual :
    Module.Free (AdjoinRoot p.val)[X] (DualNumber (AdjoinRoot p.val)[X]) :=
  Motivic.MotivicTest.PolynomialFiberNorm.dualPolynomial_finiteFree.2

/-- The new Milnor-valued theorem applies to the actual nonreduced fibers and
a varying unit, with no reduced quotient substituted for their local lengths. -/
theorem actual_nonreduced_endpoints :
    fiberValue p hp0 (DualNumber (AdjoinRoot p.val)[X])
      (Motivic.MotivicTest.PolynomialFiberNorm.varyingDualUnit (k := AdjoinRoot p.val)) 0 =
    fiberValue p hp0 (DualNumber (AdjoinRoot p.val)[X])
      (Motivic.MotivicTest.PolynomialFiberNorm.varyingDualUnit (k := AdjoinRoot p.val)) 1 :=
  fiberValue_endpoints p hp0 _ _ 0 1

/-- Both independent components of a disconnected family survive in the whole
fiber values, with no chosen branch. -/
theorem actual_two_branch_endpoints
    (v : ((AdjoinRoot p.val)[X] × (AdjoinRoot p.val)[X])ˣ) :
    fiberValue p hp0 ((AdjoinRoot p.val)[X] × (AdjoinRoot p.val)[X]) v 0 =
      fiberValue p hp0 ((AdjoinRoot p.val)[X] × (AdjoinRoot p.val)[X]) v 1 :=
  fiberValue_endpoints p hp0 _ v 0 1

/-- The actual signed endpoint difference vanishes at every integer multiplicity. -/
theorem actual_signed_endpoints {B : Type u} [CommRing B]
    [Algebra (AdjoinRoot p.val)[X] B] [Module.Finite (AdjoinRoot p.val)[X] B]
    [Module.Free (AdjoinRoot p.val)[X] B] (v : Bˣ) (n : ℤ) :
    n • (fiberValue p hp0 B v 0 - fiberValue p hp0 B v 1) = 0 := by
  rw [fiberValue_endpoints p hp0 B v 0 1, sub_self, zsmul_zero]

/-- A zero algebra gives an actual empty fiber and the zero Milnor value. -/
theorem actual_zero_fiber {B : Type u} [CommRing B] [Subsingleton B]
    [Algebra (AdjoinRoot p.val)[X] B] [Module.Finite (AdjoinRoot p.val)[X] B]
    (v : Bˣ) (a : AdjoinRoot p.val) : fiberValue p hp0 B v a = 0 := by
  rw [fiberValue_eq]
  have hn : Units.map (Algebra.norm (AdjoinRoot p.val))
      (Units.map (specialize B a).toMonoidHom v) = 1 := by
    apply Units.ext
    change Algebra.norm (AdjoinRoot p.val) (specialize B a (v : B)) = 1
    rw [Algebra.norm_apply]
    exact LinearMap.det_eq_one_of_subsingleton _
  rw [hn, symbol_one_right, map_zero]

open Lean in
run_cmd do
  for name in #[``valueVia, ``firstPolynomial, ``firstPolynomial_coeff_zero, ``firstMap,
      ``firstMap_root, ``value, ``firstPolynomial_eq, ``value_eq_valueVia,
      ``valueVia_map_degree, ``value_map_degree, ``value_one_right, ``value_one_left,
      ``value_base_first, ``value_rational, ``generatorValue, ``cycleValue,
      ``cycleValue_single, ``cycleValue_cycle, ``rootSymbolHom, ``rootSymbolHom_apply,
      ``residueValue, ``residueValue_eq, ``sum_residueValue, ``fiberValue, ``fiberValue_eq,
      ``fiberValue_endpoints, ``fiberValue_endpoints_of_torsionFree,
      ``actual_field_degree, ``actual_identity_axes, ``actual_rational,
      ``actual_signed_support, ``proper_first_coordinate, ``actual_nonreduced_fiber,
      ``actual_nonreduced_endpoints, ``actual_two_branch_endpoints,
      ``actual_signed_endpoints, ``actual_zero_fiber] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Coordinate values and whole-fiber endpoint laws use only standard foundations."

end MotivicTest.WeightTwoCoordinateEvaluation
