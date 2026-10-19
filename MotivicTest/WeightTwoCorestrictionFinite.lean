/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionFinite
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual finite-coefficient weight-two corestriction

The transfer acts on the originally defined finite motivic group and commutes
with the original integral reduction, without a level or characteristic restriction.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open WeightTwoCorestriction WeightOnePointNorm

universe w u

namespace MotivicTest.WeightTwoCorestrictionFinite

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The same original integral-reduction square holds at every natural level. -/
theorem actual_reduction (n : ℕ)
    (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) n (motivicBaseIntegralReduction E 2 2 n x) =
      motivicBaseIntegralReduction k 2 2 n (motivicCorestriction (k := k) x) :=
  finiteCorestriction_integralReduction n x

/-- Zero is an allowed coefficient level, with the same actual reduction convention. -/
theorem level_zero (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) 0 (motivicBaseIntegralReduction E 2 2 0 x) =
      motivicBaseIntegralReduction k 2 2 0 (motivicCorestriction (k := k) x) :=
  finiteCorestriction_integralReduction 0 x

/-- Composite levels need no extra invertibility or separability assumption. -/
theorem composite_level (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) 6 (motivicBaseIntegralReduction E 2 2 6 x) =
      motivicBaseIntegralReduction k 2 2 6 (motivicCorestriction (k := k) x) :=
  finiteCorestriction_integralReduction 6 x

/-- The original level-one target vanishes, including for arbitrary source classes. -/
theorem level_one
    (x : motivicFiniteCohomology E 2 2 1 (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) 1 x = 0 := by
  let := subsingleton_motivicFiniteCohomology_base_one k 2 2
  exact Subsingleton.elim _ _

/-- Signed geometric point cycles descend with the actual corestriction coefficients. -/
theorem actual_point_cycle (n : ℕ) (α : point E ⟶ WeightTwoSymbols.target E) :
    finiteCorestriction (k := k) n
      (motivicBaseIntegralReduction E 2 2 n
        ((motivicRawBaseEvaluationComparison E 2 2).symm (WeightTwoSymbols.cycleClass E α))) =
    motivicBaseIntegralReduction k 2 2 n
      ((motivicRawBaseEvaluationComparison k 2 2).symm
        (WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α))) :=
  finiteCorestriction_cycleReduction n α

open Lean in
run_cmd do
  for name in #[``motivicCorestriction_integralMultiples, ``quotientCorestriction,
      ``quotientCorestriction_mk, ``finiteCorestriction,
      ``finiteCorestriction_integralReduction, ``finiteCorestriction_unique,
      ``finiteCorestriction_rawReduction, ``finiteCorestriction_cycleReduction,
      ``actual_reduction, ``level_zero, ``composite_level, ``level_one, ``actual_point_cycle] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual finite-coefficient H22 corestriction uses only standard foundations."

end MotivicTest.WeightTwoCorestrictionFinite
