/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestriction
public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionTower

/-!
# Coherence of actual finite-extension diagonal transfers

The existing all-weight signed cycle-pushforward tower and identity equations
imply the same equations on the original raw and derived diagonal groups.
No new scheme pushforward or scalar-extension machinery is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe w u

namespace Motivic.DiagonalCorestriction

open PresheafWithTransfers DiagonalTopDegree DiagonalCycleSymbols WeightOneBoundaryNorm

section Tower

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
  [Module.Finite k L] [Module.Finite L E] [Module.Finite k E]

/-- Removing the zero simplex preserves the existing actual finite-cycle tower equation. -/
theorem pointPushforward_comp (q : ℕ) :
    (pointPushforward (k := k) (E := L) q).comp
      (pointPushforward (k := L) (E := E) q) = pointPushforward (k := k) (E := E) q := by
  ext α
  simp only [AddMonoidHom.comp_apply, pointPushforward_apply, Iso.hom_inv_id_assoc]
  exact congrArg (fun β => (zeroProductIso k).inv ≫ β)
    (DFunLike.congr_fun (WeightTwoCorestriction.cyclePushforward_comp
      (k := k) (L := L) (E := E) 0 q) ((zeroProductIso E).hom ≫ α))

/-- Actual raw diagonal corestriction composes along every finite field tower. -/
theorem corestriction_comp (q : ℕ) :
    (corestriction (k := k) (E := L) q).comp (corestriction (k := L) (E := E) q) =
      corestriction (k := k) (E := E) q := by
  apply corestriction_unique
  intro α
  simp only [AddMonoidHom.comp_apply, corestriction_cycleClass]
  exact congrArg (cycleClass k q)
    (DFunLike.congr_fun (pointPushforward_comp (k := k) (L := L) (E := E) q) α)

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The actual derived diagonal transfer retains the same original finite-field tower. -/
theorem motivicCorestriction_comp (q : ℕ) :
    (motivicCorestriction (k := k) (E := L) q).comp
      (motivicCorestriction (k := L) (E := E) q) =
        motivicCorestriction (k := k) (E := E) q := by
  ext x
  apply (motivicRawBaseEvaluationComparison k q q).injective
  simp only [AddMonoidHom.comp_apply, motivicCorestriction_comparison]
  exact DFunLike.congr_fun (corestriction_comp (k := k) (L := L) (E := E) q)
    (motivicRawBaseEvaluationComparison E q q x)

end Tower

section Identity

variable (k : Type u) [Field k]

/-- The identity scalar extension is the identity on actual signed point cycles. -/
theorem pointPushforward_id (q : ℕ) :
    pointPushforward (k := k) (E := k) q = AddMonoidHom.id _ := by
  ext α
  rw [pointPushforward_apply, WeightTwoCorestriction.cyclePushforward_id,
    AddMonoidHom.id_apply, Iso.inv_hom_id_assoc]
  rfl

/-- Identity finite-field extension acts identically on the original raw diagonal group. -/
theorem corestriction_id (q : ℕ) :
    corestriction (k := k) (E := k) q = AddMonoidHom.id _ := by
  ext x
  obtain ⟨α, rfl⟩ := cycleClass_surjective k q x
  rw [corestriction_cycleClass, pointPushforward_id]
  rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Identity finite-field extension acts identically on the original derived diagonal group. -/
theorem motivicCorestriction_id (q : ℕ) :
    motivicCorestriction (k := k) (E := k) q = AddMonoidHom.id _ := by
  ext x
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [motivicCorestriction_comparison, corestriction_id]
  rfl

end Identity

end Motivic.DiagonalCorestriction
