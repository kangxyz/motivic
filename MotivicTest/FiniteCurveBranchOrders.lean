/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.BranchOrders

/-!
# Actual scalar and whole-branch consumers

Only the original finite faithful characteristic-zero domain algebra is input.
The original curve is not assumed normal or smooth. The tests retain literal
endpoint scalars, all original residue maps, finite ENat lengths, and repeated
orders rather than passing to reduced fibers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve _root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve
open scoped Polynomial BigOperators

universe u

namespace MotivicTest.FiniteCurveBranchOrders
open _root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve

variable {k : Type u} [Field k] [CharZero k]
  (B : Type u) [CommRing B] [IsDomain B]
  [Algebra k[X] B] [Module.Finite k[X] B] [FaithfulSMul k[X] B]

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] [IsDomain B] in
/-- The normalization does not reparameterize the original affine line. -/
theorem literalParameter (a : k) (x : Spec (.of (ring B))) :
    scalar (normalizationMap B ≫ baseMap (k := k) B) a x =
      StructureSheaf.toStalk (ring B) x
        (algebraMap k[X] (ring B) (Polynomial.X - Polynomial.C a)) := by
  rw [normalizationMap_baseMap, scalar_specMap]

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] [IsDomain B] in
/-- The zero endpoint uses the actual original parameter. -/
theorem zeroParameter (x : Spec (.of (ring B))) :
    scalar (normalizationMap B ≫ baseMap (k := k) B) 0 x =
      StructureSheaf.toStalk (ring B) x (algebraMap k[X] (ring B) Polynomial.X) := by
  simp only [literalParameter, Polynomial.C_0, sub_zero]
  rfl

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] [IsDomain B] in
/-- The one endpoint keeps its subtraction by the original constant one. -/
theorem oneParameter (x : Spec (.of (ring B))) :
    scalar (normalizationMap B ≫ baseMap (k := k) B) 1 x =
      StructureSheaf.toStalk (ring B) x
        (algebraMap k[X] (ring B) (Polynomial.X - 1)) := by
  simp only [literalParameter, Polynomial.C_1]
  rfl

variable (a : k) (y : fiber (baseMap (k := k) B) a)
  (x : {x : Spec (.of (ring B)) //
    normalizationMap B x = fiberInclusion (baseMap (k := k) B) a y})

/-- The local DVR is a conclusion for every actual branch. -/
theorem actualBranchDVR : IsDiscreteValuationRing ((Spec (.of (ring B))).presheaf.stalk x.1) :=
  branch_stalk_isDiscreteValuationRing B a y x

/-- Actual branch orders are finite in ENat before cycle conversion. -/
theorem actualBranchFinite : branchOrder B a y x ≠ ⊤ := branchOrder_ne_top B a y x

/-- Repeating the literal endpoint equation preserves every repeated order. -/
theorem repeatedEndpointLength (n : ℕ) :
    Module.length ((Spec (.of (ring B))).presheaf.stalk x.1)
      (((Spec (.of (ring B))).presheaf.stalk x.1) ⧸
        Ideal.ofList [(scalar (normalizationMap B ≫ baseMap (k := k) B) a x.1) ^ n]) =
      n • branchOrder B a y x := by
  let := branch_stalk_isDiscreteValuationRing B a y x
  rw [IsDiscreteValuationRing.length_quotient_ofList_eq_addVal _
    (pow_ne_zero n (normalization_scalar_ne_zero B a x.1)), IsDiscreteValuationRing.addVal_pow]
  rfl

/-- The coefficient has the whole actual branch index and original residue map. -/
theorem allBranchCoefficient :
    letI : IsNoetherian (Spec (.of B)) := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType
        (baseMap (k := k) B)
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.toPoints
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (fiber (baseMap (k := k) B) a)) y =
      ∑ᶠ z : {z : Spec (.of (ring B)) //
        normalizationMap B z = fiberInclusion (baseMap (k := k) B) a y},
        ((normalizationMap B).residueDegree z.1 : ℤ) * (branchOrder B a y z).toNat :=
  fiber_fundamentalCoefficient_eq_sum_branchOrders B a y

omit [CharZero k] [Module.Finite k[X] B] [FaithfulSMul k[X] B] [IsDomain B] in
/-- The normalized endpoint residue weight is the literal normalization weight. -/
theorem actualResidueMap (z : fiber (normalizationMap B ≫ baseMap (k := k) B) a) :
    (fiberMap (baseMap (k := k) B) a (normalizationMap B)).residueDegree z =
      (normalizationMap B).residueDegree
        (fiberInclusion (normalizationMap B ≫ baseMap (k := k) B) a z) :=
  fiberMap_residueDegree (baseMap (k := k) B) a (normalizationMap B) z

open Lean in
run_cmd do
  for name in #[``scalar_specMap, ``scalar_specMap_ne_zero, ``endpoint_prime_ne_bot,
      ``endpoint_stalk_isDiscreteValuationRing,
          ``_root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve.ring_faithfulSMul_base,
      ``branch_scalar_mem_maximalIdeal, ``branch_stalk_isDiscreteValuationRing,
      ``normalization_scalar_ne_zero,
          ``_root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve.branchOrder,
          ``_root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve.branchOrder_ne_top,
      ``branch_cartierLength_eq_order,
          ``_root_.AlgebraicGeometry.Scheme.Normalization.FiniteCurve.normalizedPointBranch,
      ``normalization_fiber_fundamentalCoefficient_eq_order,
      ``fiber_fundamentalCoefficient_eq_sum_branchOrders, ``cartierLength_eq_sum_branchOrders,
      ``literalParameter, ``zeroParameter, ``oneParameter, ``actualBranchDVR,
      ``actualBranchFinite, ``repeatedEndpointLength, ``allBranchCoefficient,
      ``actualResidueMap] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual normalization branch orders and fiber coefficients use only standard foundations."

end MotivicTest.FiniteCurveBranchOrders
