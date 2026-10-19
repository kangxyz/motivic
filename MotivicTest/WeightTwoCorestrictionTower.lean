/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionTower
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual finite weight-two transfer tower

These consumers use the original finite scalar maps, signed correspondences and
raw, derived and finite-coefficient motivic groups. No norm-compatibility
hypothesis, replacement cohomology group or separability assumption is supplied.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open WeightTwoCorestriction WeightOnePointNorm WeightOneBoundaryNorm

universe w u

namespace MotivicTest.WeightTwoCorestrictionTower

section Tower

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
  [Module.Finite k L] [Module.Finite L E] [Module.Finite k E]

omit [Module.Finite k L] [Module.Finite L E] [Module.Finite k E] in
/-- The actual ambient scheme map, in any singular degree and torus rank, composes. -/
theorem actual_ambient_tower (r q : ℕ) :
    ambientMap (k := L) (E := E) r q ≫ ambientMap (k := k) (E := L) r q =
      ambientMap (k := k) (E := E) r q := ambientMap_comp r q

/-- All signed cycles, including sums whose finite images collide, obey the tower. -/
theorem actual_signed_cycle_tower (r q : ℕ) (n : ℤ)
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E q)) :
    cyclePushforward (k := k) (E := L) r q
      (cyclePushforward (k := L) (E := E) r q (n • α)) =
        n • cyclePushforward (k := k) (E := E) r q α := by
  rw [← AddMonoidHom.comp_apply, cyclePushforward_comp, map_zsmul]

/-- The exact zero-simplex isomorphisms are retained for actual point cycles. -/
theorem actual_point_tower (α : point E ⟶ WeightTwoSymbols.target E) :
    pointPushforward (k := k) (E := L) (pointPushforward (k := L) (E := E) α) =
      pointPushforward (k := k) (E := E) α :=
  DFunLike.congr_fun (pointPushforward_comp (k := k) (L := L) (E := E)) α

/-- The tower equality holds for every class of the original raw H22. -/
theorem actual_raw_homology_tower (x : (motivicRawBaseComplex E 2).homology 2) :
    corestriction (k := k) (E := L) (corestriction (k := L) (E := E) x) =
      corestriction (k := k) (E := E) x :=
  DFunLike.congr_fun (corestriction_comp (k := k) (L := L) (E := E)) x

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The derived tower is an equality on the original motivic group. -/
theorem actual_derived_tower
    (x : motivicCohomology E 2 2 (SmoothSite.base (Spec (.of E)))) :
    motivicCorestriction (k := k) (E := L) (motivicCorestriction (k := L) (E := E) x) =
      motivicCorestriction (k := k) (E := E) x :=
  DFunLike.congr_fun (motivicCorestriction_comp (k := k) (L := L) (E := E)) x

/-- Every natural coefficient level has the same tower, without characteristic restrictions. -/
theorem actual_finite_tower (n : ℕ)
    (x : motivicFiniteCohomology E 2 2 n (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) (E := L) n (finiteCorestriction (k := L) (E := E) n x) =
      finiteCorestriction (k := k) (E := E) n x :=
  DFunLike.congr_fun (finiteCorestriction_comp (k := k) (L := L) (E := E) n) x

end Derived
end Tower

section Identity

variable (k : Type u) [Field k]

/-- Identity transfer fixes every original raw homology class. -/
theorem actual_raw_identity (x : (motivicRawBaseComplex k 2).homology 2) :
    corestriction (k := k) (E := k) x = x :=
  DFunLike.congr_fun (corestriction_id k) x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Identity transfer fixes every finite-coefficient class, also at level zero. -/
theorem actual_finite_identity (n : ℕ)
    (x : motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k)))) :
    finiteCorestriction (k := k) (E := k) n x = x :=
  DFunLike.congr_fun (finiteCorestriction_id k n) x

end Identity

open Lean in
run_cmd do
  for name in #[``sourceMap_comp, ``torusMap_comp, ``ambientMap_comp,
      ``sourceMap_id, ``torusMap_id, ``ambientMap_id, ``imageGenerator_comp,
      ``ambientMap_residueDegree_comp, ``cyclePushforward_comp,
      ``reducedPushforward_comp, ``pointPushforward_comp, ``rawDegreeOnePushforward_comp,
      ``rawDegreeTwoPushforward_comp, ``corestriction_comp, ``motivicCorestriction_comp,
      ``finiteCorestriction_comp, ``cyclePushforward_id, ``pointPushforward_id,
      ``corestriction_id, ``motivicCorestriction_id, ``finiteCorestriction_id,
      ``actual_ambient_tower, ``actual_signed_cycle_tower, ``actual_point_tower,
      ``actual_raw_homology_tower, ``actual_derived_tower, ``actual_finite_tower,
      ``actual_raw_identity, ``actual_finite_identity] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-two corestriction towers use only standard foundations."

end MotivicTest.WeightTwoCorestrictionTower
