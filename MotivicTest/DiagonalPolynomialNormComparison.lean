/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.PolynomialNormComparison
public import Lean.Util.CollectAxioms

/-!
# Consumers of the general degree-two norm and actual H²,² comparison

The input is the all-degree Milnor quotient, not the old K₂ presentation.
The target maps are the actual general diagonal symbol and original motivic
corestriction maps. Characteristic zero and both derived-category hypotheses
are retained explicitly. Zero and composite coefficient levels are exercised.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Polynomial Motivic
open MilnorK MilnorK.PolynomialResidue
open MilnorK.PolynomialNorm DiagonalMilnorSymbol WeightTwoCorestriction
open DiagonalPolynomialNormComparison

universe w u

namespace MotivicTest.DiagonalPolynomialNormComparison

variable {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance : Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- The general presentation's norm reaches the actual raw weight-two group. -/
theorem actual_raw (x : K (AdjoinRoot p.val) 2) :
    (rawSymbol k 2 (polynomialNorm 2 p x) : (motivicRawBaseComplex k 2).homology 2) =
      corestriction (k := k) (rawSymbol (AdjoinRoot p.val) 2 x) :=
  raw_norm p x

/-- The full raw square has no class-generation premise. -/
theorem actual_raw_square :
    (rawSymbol k 2).comp (polynomialNorm 2 p).toAddMonoidHom =
      (corestriction (k := k) (E := AdjoinRoot p.val)).comp (rawSymbol (AdjoinRoot p.val) 2) :=
  raw_norm_square p

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1})]

/-- The full derived square retains both original derived-category hypotheses. -/
theorem actual_derived (x : K (AdjoinRoot p.val) 2) :
    (motivicSymbol k 2 (polynomialNorm 2 p x) :
        motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) =
      motivicCorestriction (k := k) (motivicSymbol (AdjoinRoot p.val) 2 x) :=
  derived_norm p x

/-- Every natural coefficient level gives the original finite-coefficient square. -/
theorem actual_finite (n : ℕ) (x : K (AdjoinRoot p.val) 2) :
    (motivicBaseIntegralReduction k 2 2 n (motivicSymbol k 2 (polynomialNorm 2 p x)) :
        motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) =
      finiteCorestriction (k := k) n
        (motivicBaseIntegralReduction (AdjoinRoot p.val) 2 2 n
          (motivicSymbol (AdjoinRoot p.val) 2 x)) :=
  finite_norm p n x

/-- Level zero is included without any positivity premise. -/
theorem actual_finite_zero (x : K (AdjoinRoot p.val) 2) :
    motivicBaseIntegralReduction k 2 2 0 (motivicSymbol k 2 (polynomialNorm 2 p x)) =
      finiteCorestriction (k := k) 0
        (motivicBaseIntegralReduction (AdjoinRoot p.val) 2 2 0
          (motivicSymbol (AdjoinRoot p.val) 2 x)) :=
  finite_norm p 0 x

/-- Composite level four is included without a primality premise. -/
theorem actual_finite_composite (x : K (AdjoinRoot p.val) 2) :
    motivicBaseIntegralReduction k 2 2 4 (motivicSymbol k 2 (polynomialNorm 2 p x)) =
      finiteCorestriction (k := k) 4
        (motivicBaseIntegralReduction (AdjoinRoot p.val) 2 2 4
          (motivicSymbol (AdjoinRoot p.val) 2 x)) :=
  finite_norm p 4 x

open Lean in
run_cmd do
  for name in #[``Motivic.DiagonalPolynomialNormComparison.raw_norm,
      ``Motivic.DiagonalPolynomialNormComparison.raw_norm_square,
      ``Motivic.DiagonalPolynomialNormComparison.derived_norm,
      ``Motivic.DiagonalPolynomialNormComparison.finite_norm,
      ``actual_raw, ``actual_raw_square, ``actual_derived, ``actual_finite,
      ``actual_finite_zero, ``actual_finite_composite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The general degree-two norm and actual H22 use only standard Lean logical foundations."

end MotivicTest.DiagonalPolynomialNormComparison
