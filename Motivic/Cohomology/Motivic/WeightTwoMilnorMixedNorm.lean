/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialNormProjection
public import Motivic.Cohomology.Motivic.WeightTwoMilnorSymbol
public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionMixed
public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionFinite

/-!
# Actual Milnor/motivic norm compatibility on arbitrary mixed symbols

The constructed polynomial Milnor norm agrees with the original finite
corestriction on every symbol whose second coordinate comes from the base
field. The first coordinate is an arbitrary unit of the original quotient
field. The equality holds in the actual raw, derived integral, and finite
coefficient groups. General two-coordinate compatibility is a separate goal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe w u

namespace Motivic.WeightTwoMilnorMixedNorm

open MilnorK.K2 MilnorK.K3.PolynomialResidue
open MilnorK.K3.PolynomialNorm WeightTwoMilnorSymbol WeightTwoCorestriction

variable {k : Type u} [Field k] [CharZero k] (p : MonicIrreducible k)

local instance finite_root : Module.Finite k (AdjoinRoot p.val) := p.property.1.finite_adjoinRoot

local instance charZero_root : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- The original raw Milnor symbol intertwines the two actual transfers on
the arbitrary-unit/base-constant symbol. -/
theorem raw_mixed (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    rawMilnorSymbol k (polynomialNorm p
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) =
    corestriction (k := k) (rawMilnorSymbol (AdjoinRoot p.val)
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) := by
  rw [polynomialNorm_symbol_constant, rawMilnorSymbol_symbol, rawMilnorSymbol_symbol,
    corestriction_graphSymbol_append]

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (AdjoinRoot p.val)))) AddCommGrpCat.{u + 1})]

/-- The same equality holds in the originally defined derived motivic group. -/
theorem derived_mixed (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    motivicMilnorSymbol k (polynomialNorm p
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) =
    motivicCorestriction (k := k) (motivicMilnorSymbol (AdjoinRoot p.val)
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) := by
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  rw [motivicMilnorSymbol_comparison, motivicCorestriction_comparison,
    motivicMilnorSymbol_comparison, raw_mixed]

/-- Original coefficient reduction preserves this compatibility at every
natural level, including zero, one, and composite levels. -/
theorem finite_mixed (n : ℕ) (a : (AdjoinRoot p.val)ˣ) (b : kˣ) :
    finiteMilnorSymbol k n (polynomialNorm p
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) =
    finiteCorestriction (k := k) n (finiteMilnorSymbol (AdjoinRoot p.val) n
      (symbol a (Units.map (algebraMap k (AdjoinRoot p.val)).toMonoidHom b))) := by
  change motivicBaseIntegralReduction k 2 2 n (motivicMilnorSymbol k _) =
    finiteCorestriction (k := k) n
      (motivicBaseIntegralReduction (AdjoinRoot p.val) 2 2 n (motivicMilnorSymbol _ _))
  rw [finiteCorestriction_integralReduction, derived_mixed]

end Motivic.WeightTwoMilnorMixedNorm
