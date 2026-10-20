/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.MilnorRootNorm
public import Lean.Util.CollectAxioms

/-! # Consumers of the actual root-symbol norm comparison -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open MilnorK.K2 MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm Motivic.WeightTwoMilnorSymbol
open Motivic.WeightTwoCorestriction Motivic.WeightTwoMilnorRootNorm

universe u

namespace MotivicTest.WeightTwoMilnorRootNorm

variable {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- Both original transfers agree on the specified symbol in actual raw homology. -/
theorem actual_raw (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    (rawMilnorSymbol k (polynomialNorm p
      (symbol (rootUnit p hp0) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :
        (motivicRawBaseComplex k 2).homology 2) =
      corestriction (k := k) (rawMilnorSymbol (AdjoinRoot p.val)
        (symbol (rootUnit p hp0) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :=
  raw_root_constant p hp0 b

/-- Use the standard derived category of Nisnevich sheaves over the base field in this test. -/
local instance instHasDerivedCategoryMotivicTest : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- Use the standard derived category of Nisnevich sheaves over the root field in this test. -/
local instance instHasDerivedCategoryAdjoinRootMotivicTest : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The target is the original derived integral group, rather than a new presentation. -/
theorem actual_derived (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    (motivicMilnorSymbol k (polynomialNorm p
      (symbol (rootUnit p hp0) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :
        motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) =
      motivicCorestriction (k := k) (motivicMilnorSymbol (AdjoinRoot p.val)
        (symbol (rootUnit p hp0) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :=
  derived_root_constant p hp0 b

/-- Every coefficient level retains the original finite group and actual reduction. -/
theorem actual_finite (n : ℕ) (hp0 : p.val.coeff 0 ≠ 0) (b : kˣ) :
    (finiteMilnorSymbol k n (polynomialNorm p
      (symbol (rootUnit p hp0) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :
        motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) =
      finiteCorestriction (k := k) n (finiteMilnorSymbol (AdjoinRoot p.val) n
        (symbol (rootUnit p hp0) (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :=
  finite_root_constant p n hp0 b

open Lean in
run_cmd do
  for name in #[``Motivic.WeightTwoMilnorRootNorm.raw_root_constant,
      ``Motivic.WeightTwoMilnorRootNorm.derived_root_constant,
      ``Motivic.WeightTwoMilnorRootNorm.finite_root_constant,
      ``actual_raw, ``actual_derived, ``actual_finite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual root-symbol norm comparisons use only standard Lean logical foundations."

end MotivicTest.WeightTwoMilnorRootNorm
