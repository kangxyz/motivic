/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMilnorNormComparison
public import Lean.Util.CollectAxioms

/-!
# Consumers of the full actual polynomial norm comparison

Every input belongs to the original Milnor K₂ group, and every target is the
original raw, derived integral, or finite-coefficient motivic group. Neither
mixed-symbol generation nor transfer compatibility is an input hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Motivic
open MilnorK.K2 MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm Motivic.WeightTwoMilnorSymbol
open Motivic.WeightTwoCorestriction Motivic.WeightTwoMilnorNormComparison

universe u

namespace MotivicTest.WeightTwoMilnorNormComparison

variable {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- The full actual raw comparison holds for every original Milnor element. -/
theorem actual_raw (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    (rawMilnorSymbol k (polynomialNorm p x) :
        (motivicRawBaseComplex k 2).homology 2) =
      corestriction (k := k) (rawMilnorSymbol (AdjoinRoot p.val) x) :=
  raw_norm p x

/-- Both coordinates are unrestricted original quotient-field units. -/
theorem actual_arbitrary_symbol (a b : (AdjoinRoot p.val)ˣ) :
    rawMilnorSymbol k (polynomialNorm p (symbol a b)) =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot p.val) a b) :=
  raw_norm p (symbol a b)

local instance : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

local instance : HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The comparison uses the original derived integral motivic cohomology. -/
theorem actual_derived (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    (motivicMilnorSymbol k (polynomialNorm p x) :
        motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) =
      motivicCorestriction (k := k) (motivicMilnorSymbol (AdjoinRoot p.val) x) :=
  derived_norm p x

/-- All natural coefficient levels, including composite levels, are retained. -/
theorem actual_finite (n : ℕ) (x : MilnorK.K2.Group (AdjoinRoot p.val)) :
    (finiteMilnorSymbol k n (polynomialNorm p x) :
        motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) =
      finiteCorestriction (k := k) n (finiteMilnorSymbol (AdjoinRoot p.val) n x) :=
  finite_norm p n x

open Lean in
run_cmd do
  for name in #[``Motivic.WeightTwoMilnorNormComparison.raw_norm_degree_one,
      ``Motivic.WeightTwoMilnorNormComparison.raw_norm,
      ``Motivic.WeightTwoMilnorNormComparison.derived_norm,
      ``Motivic.WeightTwoMilnorNormComparison.finite_norm,
      ``actual_raw, ``actual_arbitrary_symbol, ``actual_derived, ``actual_finite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Full actual Milnor norm comparisons use only standard Lean logical foundations."

end MotivicTest.WeightTwoMilnorNormComparison
