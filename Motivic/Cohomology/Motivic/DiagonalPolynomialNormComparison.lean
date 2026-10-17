/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.KTheory.MilnorK.PolynomialNormCompatibility
public import Motivic.Cohomology.Motivic.DiagonalMilnorSymbol
public import Motivic.Cohomology.Motivic.WeightTwoMilnorNormComparison

/-!
# The general degree-two norm and the actual diagonal motivic symbol

The all-degree Milnor presentation and its actual polynomial norm inherit the
proved weight-two norm comparison through the full presentation equivalence.
The maps here are the existing general diagonal graph-symbol maps and the
original raw, derived integral, and finite-coefficient motivic corestrictions.
The motivic comparison retains characteristic zero; the derived statements
retain both derived-category hypotheses. This is a degree-two comparison for
a specified polynomial presentation, not an all-weight transfer theorem.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe w u

namespace Motivic.DiagonalPolynomialNormComparison

open KTheory.MilnorK KTheory.MilnorK.PolynomialResidue
open KTheory.MilnorK.PolynomialNorm DiagonalMilnorSymbol WeightTwoCorestriction

variable {k : Type u} [Field k] [CharZero k]

local instance finite_root (p : MonicIrreducible k) :
    Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance charZero_root (p : MonicIrreducible k) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- The actual general degree-two polynomial norm intertwines the raw diagonal
symbol and original motivic corestriction on every quotient class. -/
theorem raw_norm (p : MonicIrreducible k) (x : K (AdjoinRoot p.val) 2) :
    rawSymbol k 2 (polynomialNorm 2 p x) =
      corestriction (k := k) (E := AdjoinRoot p.val) (rawSymbol (AdjoinRoot p.val) 2 x) := by
  rw [rawSymbol_two_comparison k, twoEquiv_polynomialNorm,
    WeightTwoMilnorNormComparison.raw_norm, rawSymbol_two_comparison (AdjoinRoot p.val)]

/-- The raw comparison is an equality of the actual additive map composites. -/
theorem raw_norm_square (p : MonicIrreducible k) :
    (rawSymbol k 2).comp (polynomialNorm 2 p).toAddMonoidHom =
      (corestriction (k := k) (E := AdjoinRoot p.val)).comp (rawSymbol (AdjoinRoot p.val) 2) :=
  AddMonoidHom.ext (raw_norm p)

variable (p : MonicIrreducible k)
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1})]

/-- The same norm comparison holds in the original derived diagonal group H²,². -/
theorem derived_norm (x : K (AdjoinRoot p.val) 2) :
    motivicSymbol k 2 (polynomialNorm 2 p x) =
      motivicCorestriction (k := k) (motivicSymbol (AdjoinRoot p.val) 2 x) := by
  rw [motivicSymbol_two_comparison k, twoEquiv_polynomialNorm,
    WeightTwoMilnorNormComparison.derived_norm,
    motivicSymbol_two_comparison (AdjoinRoot p.val)]

/-- The original coefficient reduction preserves the comparison for every
natural level, without a prime, nonzero, or invertibility restriction. -/
theorem finite_norm (n : ℕ) (x : K (AdjoinRoot p.val) 2) :
    motivicBaseIntegralReduction k 2 2 n (motivicSymbol k 2 (polynomialNorm 2 p x)) =
      finiteCorestriction (k := k) n
        (motivicBaseIntegralReduction (AdjoinRoot p.val) 2 2 n
          (motivicSymbol (AdjoinRoot p.val) 2 x)) := by
  rw [finiteCorestriction_integralReduction, derived_norm]

end Motivic.DiagonalPolynomialNormComparison
