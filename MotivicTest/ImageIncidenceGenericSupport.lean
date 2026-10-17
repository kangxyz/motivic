/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.ImageIncidenceGenericSupport

/-!
# Global actual image-incidence support consumers

These consumers use arbitrary-field smooth objects and the original triple Tor
cycle. They require no generic-preservation premise, purity, separability,
flatness of supports, or injectivity of component images. The arbitrary signed
coefficient statement also tests that the global result is collision-aware.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ImageIncidenceGenericSupport

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Both actual image-incidence targets are finite over the original source. -/
theorem actualImageIncidenceSourceFinite :
    IsFinite (F.leftImageIncidenceSource G H) ∧
      IsFinite (F.rightImageIncidenceSource G H) :=
  ⟨F.isFinite_leftImageIncidenceSource k G H, F.isFinite_rightImageIncidenceSource k G H⟩

/-- Both composites retain the same original triple source map. -/
theorem actualSourceComposites :
    F.tripleToLeftImageIncidence G H ≫ F.leftImageIncidenceSource G H =
        F.tripleIncidenceSource G H ∧
      F.tripleToRightImageIncidence G H ≫ F.rightImageIncidenceSource G H =
        F.tripleIncidenceSource G H :=
  ⟨F.tripleToLeftImageIncidence_source G H, F.tripleToRightImageIncidence_source G H⟩

/-- Every source generic lands in genuine target generic support in both orders. -/
theorem actualGenericTargets (w : genericPoints (F.tripleIncidence G H)) :
    F.tripleToLeftImageIncidence G H w.1 ∈ genericPoints (F.leftImageIncidence G H) ∧
      F.tripleToRightImageIncidence G H w.1 ∈ genericPoints (F.rightImageIncidence G H) :=
  ⟨F.tripleToLeftImageIncidence_mem_genericPoints k G H w.1 w.2,
    F.tripleToRightImageIncidence_mem_genericPoints k G H w.1 w.2⟩

/-- No coefficient at a nongeneric right target is silently omitted. -/
theorem actualRightOffGenericZero (y : F.rightImageIncidence G H)
    (hy : y ∉ genericPoints (F.rightImageIncidence G H)) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y = 0 :=
  F.rightImageIncidenceTorCycleCoefficient_eq_zero_of_not_generic k G H y hy

/-- The left order satisfies the same actual off-generic check. -/
theorem actualLeftOffGenericZero (y : F.leftImageIncidence G H)
    (hy : y ∉ genericPoints (F.leftImageIncidence G H)) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y = 0 :=
  F.leftImageIncidenceTorCycleCoefficient_eq_zero_of_not_generic k G H y hy

/-- Signed coefficients and collisions are allowed in the global left expression. -/
theorem actualSignedLeftGlobalExpression
    (c : genericPoints (F.tripleIncidence G H) → ℤ) :
    IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
        (IntegralCycle.ofGenericCoefficients (F.tripleIncidence G H) c) =
      IntegralCycle.ofGenericCoefficients (F.leftImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToLeftImageIncidence G H) c y.1) :=
  F.finitePushforward_tripleToLeftImageIncidence_ofGenericCoefficients k G H c

/-- Signed coefficients and collisions are also allowed in the right expression. -/
theorem actualSignedRightGlobalExpression
    (c : genericPoints (F.tripleIncidence G H) → ℤ) :
    IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
        (IntegralCycle.ofGenericCoefficients (F.tripleIncidence G H) c) =
      IntegralCycle.ofGenericCoefficients (F.rightImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToRightImageIncidence G H) c y.1) :=
  F.finitePushforward_tripleToRightImageIncidence_ofGenericCoefficients k G H c

/-- The full canonical triple Tor cycle has a global right generic expression. -/
theorem actualTripleTorRightGlobalExpression :
    IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
        (F.tripleIncidenceTorCycle k G H) =
      IntegralCycle.ofGenericCoefficients (F.rightImageIncidence G H)
        (fun y => IntegralCycle.genericPushforwardCoefficient
          (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H) y.1) :=
  F.finitePushforward_tripleTorCycle_rightImageIncidence k G H

end MotivicTest.ImageIncidenceGenericSupport
