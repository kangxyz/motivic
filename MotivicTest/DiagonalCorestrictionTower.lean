/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCorestrictionTower
public import Lean.Util.CollectAxioms

/-!
# Consumers of all-weight transfer coherence

The finite-field tower keeps the original raw and derived diagonal groups;
identity transfer is checked for arbitrary weights. Every tested declaration
is checked recursively for standard foundations only.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Motivic.DiagonalCorestriction

universe w u

namespace MotivicTest.DiagonalCorestrictionTower

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
  [Module.Finite k L] [Module.Finite L E] [Module.Finite k E]

/-- Iterated actual raw transfers equal direct transfer over the original finite tower. -/
theorem actual_raw_tower (q : ℕ) (x : (motivicRawBaseComplex E q).homology q) :
    corestriction (k := k) (E := L) q (corestriction (k := L) (E := E) q x) =
      corestriction (k := k) (E := E) q x :=
  DFunLike.congr_fun (corestriction_comp (k := k) (L := L) (E := E) q) x

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The same composition holds on the original derived diagonal cohomology. -/
theorem actual_derived_tower (q : ℕ)
    (x : motivicCohomology E q q (SmoothSite.base (Spec (.of E)))) :
    motivicCorestriction (k := k) (E := L) q (motivicCorestriction (k := L) (E := E) q x) =
      motivicCorestriction (k := k) (E := E) q x :=
  DFunLike.congr_fun (motivicCorestriction_comp (k := k) (L := L) (E := E) q) x

open Lean in
run_cmd do
  for name in #[``pointPushforward_comp, ``corestriction_comp, ``motivicCorestriction_comp,
      ``pointPushforward_id, ``corestriction_id, ``motivicCorestriction_id,
      ``actual_raw_tower, ``actual_derived_tower] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight transfer coherence uses only standard foundations."

end MotivicTest.DiagonalCorestrictionTower
