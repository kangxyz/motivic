/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionHomology

/-!
# Actual finite-coefficient weight-two corestriction

The original integral corestriction preserves the actual subgroup of `n`-multiples.
It therefore descends through the existing top-degree coefficient comparison to
actual motivic `H^{2,2}(-, ℤ/n)`. The defining square uses the original integral
reduction. Every natural level is allowed, including zero, one, composite levels
and levels divisible by the field characteristic.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Motivic.WeightTwoCorestriction
open _root_.AlgebraicGeometry.Scheme

open FieldTopDegree WeightOnePointNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The same integral transfer preserves the actual coefficient relation subgroup. -/
theorem motivicCorestriction_integralMultiples (n : ℕ) :
    integralMultiples E 2 n ≤
      (integralMultiples k 2 n).comap (motivicCorestriction (k := k) (E := E)) := by
  intro x hx
  obtain ⟨y, hy⟩ := (mem_integralMultiples E 2 n x).mp hx
  change motivicCorestriction (k := k) x ∈ integralMultiples k 2 n
  apply (mem_integralMultiples k 2 n _).mpr
  refine ⟨motivicCorestriction (k := k) y, ?_⟩
  exact ((motivicCorestriction (k := k) (E := E)).map_nsmul n y).symm.trans
    (congrArg (motivicCorestriction (k := k) (E := E)) hy)

/-- The integral transfer on the original quotient by coefficient multiples. -/
def quotientCorestriction (n : ℕ) : integralModulo E 2 n →+ integralModulo k 2 n :=
  QuotientAddGroup.map (integralMultiples E 2 n) (integralMultiples k 2 n)
    (motivicCorestriction (k := k) (E := E)) (motivicCorestriction_integralMultiples n)

/-- The quotient transfer retains the original integral representative. -/
theorem quotientCorestriction_mk (n : ℕ)
    (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    quotientCorestriction (k := k) n (QuotientAddGroup.mk x) =
      (QuotientAddGroup.mk (motivicCorestriction (k := k) x) : integralModulo k 2 n) := rfl

/-- Corestriction on the actual finite-coefficient motivic cohomology group. -/
def finiteCorestriction (n : ℕ) :
    motivicFiniteCohomology E 2 2 n (SmoothSite.base (Spec (.of E))) →+
      motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k))) :=
  (topDegreeFiniteEquiv k 2 n).symm.toAddMonoidHom.comp
    ((quotientCorestriction (k := k) (E := E) n).comp
      (topDegreeFiniteEquiv E 2 n).toAddMonoidHom)

/-- Original integral reduction commutes with the actual finite transfer. -/
theorem finiteCorestriction_integralReduction (n : ℕ)
    (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) n (motivicBaseIntegralReduction E 2 2 n x) =
      motivicBaseIntegralReduction k 2 2 n (motivicCorestriction (k := k) x) := by
  change (topDegreeFiniteEquiv k 2 n).symm
    (quotientCorestriction (k := k) n
      (topDegreeFiniteEquiv E 2 n (motivicBaseIntegralReduction E 2 2 n x))) = _
  exact (congrArg (fun y => (topDegreeFiniteEquiv k 2 n).symm
    (quotientCorestriction (k := k) (E := E) n y))
      (topDegreeFiniteEquiv_integralReduction E 2 n x)).trans
        (topDegreeFiniteEquiv_symm_mk k 2 n _)

/-- The finite map is uniquely determined by its original integral reduction square. -/
theorem finiteCorestriction_unique (n : ℕ)
    (f : motivicFiniteCohomology E 2 2 n (SmoothSite.base (Spec (.of E))) →+
      motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k))))
    (hf : ∀ x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E))),
      f (motivicBaseIntegralReduction E 2 2 n x) =
        motivicBaseIntegralReduction k 2 2 n (motivicCorestriction (k := k) x)) :
    f = finiteCorestriction (k := k) (E := E) n := by
  ext x
  obtain ⟨y, rfl⟩ := integralReduction_surjective E 2 n x
  exact (hf y).trans (finiteCorestriction_integralReduction n y).symm

/-- Raw integral classes reduce through the same genuine derived comparison. -/
theorem finiteCorestriction_rawReduction (n : ℕ)
    (x : (motivicRawBaseComplex E 2).homology 2) :
    finiteCorestriction (k := k) n
      (motivicBaseIntegralReduction E 2 2 n
        ((motivicRawBaseEvaluationComparison E 2 2).symm x)) =
    motivicBaseIntegralReduction k 2 2 n
      ((motivicRawBaseEvaluationComparison k 2 2).symm (corestriction (k := k) x)) := by
  rw [finiteCorestriction_integralReduction]
  change motivicBaseIntegralReduction k 2 2 n
    ((motivicRawBaseEvaluationComparison k 2 2).symm
      (corestriction (k := k) (motivicRawBaseEvaluationComparison E 2 2
        ((motivicRawBaseEvaluationComparison E 2 2).symm x)))) = _
  rw [AddEquiv.apply_symm_apply]

/-- The full signed point-cycle formula descends to every natural coefficient level. -/
theorem finiteCorestriction_cycleReduction (n : ℕ)
    (α : point E ⟶ WeightTwoSymbols.target E) :
    finiteCorestriction (k := k) n
      (motivicBaseIntegralReduction E 2 2 n
        ((motivicRawBaseEvaluationComparison E 2 2).symm (WeightTwoSymbols.cycleClass E α))) =
    motivicBaseIntegralReduction k 2 2 n
      ((motivicRawBaseEvaluationComparison k 2 2).symm
        (WeightTwoSymbols.cycleClass k (pointPushforward (k := k) α))) := by
  rw [finiteCorestriction_rawReduction, corestriction_cycleClass]

end Motivic.WeightTwoCorestriction
