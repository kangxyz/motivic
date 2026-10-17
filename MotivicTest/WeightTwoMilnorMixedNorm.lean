/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMilnorMixedNorm
public import Lean.Util.CollectAxioms

/-! # Consumers of the actual mixed-symbol norm comparison -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Motivic
open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK3.PolynomialResidue
open Motivic.KTheory.MilnorK3.PolynomialNorm Motivic.WeightTwoMilnorSymbol
open Motivic.WeightTwoCorestriction Motivic.WeightTwoMilnorMixedNorm

universe u

namespace MotivicTest.WeightTwoMilnorMixedNorm

variable {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- Both original transfers agree on the specified symbol in actual raw homology. -/
theorem actual_raw (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    (rawMilnorSymbol k (polynomialNorm p
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :
        (motivicRawBaseComplex k 2).homology 2) =
      corestriction (k := k) (rawMilnorSymbol (AdjoinRoot p.val)
        (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :=
  raw_mixed p a b

local instance : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

local instance : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The target is the original derived integral group, rather than a new presentation. -/
theorem actual_derived (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    (motivicMilnorSymbol k (polynomialNorm p
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :
        motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) =
      motivicCorestriction (k := k) (motivicMilnorSymbol (AdjoinRoot p.val)
        (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :=
  derived_mixed p a b

/-- Every coefficient level retains the original finite group and actual reduction. -/
theorem actual_finite (n : ℕ) (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    (finiteMilnorSymbol k n (polynomialNorm p
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :
        motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) =
      finiteCorestriction (k := k) n (finiteMilnorSymbol (AdjoinRoot p.val) n
        (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) :=
  finite_mixed p n a b

open Lean in
run_cmd do
  for name in #[``Motivic.WeightTwoMilnorMixedNorm.raw_mixed,
      ``Motivic.WeightTwoMilnorMixedNorm.derived_mixed,
      ``Motivic.WeightTwoMilnorMixedNorm.finite_mixed,
      ``actual_raw, ``actual_derived, ``actual_finite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual mixed-symbol norm comparisons use only standard Lean logical foundations."

end MotivicTest.WeightTwoMilnorMixedNorm
