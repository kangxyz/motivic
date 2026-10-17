/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OriginalGermEtalePullback
public import Lean.Util.CollectAxioms

/-! Regression checks for étale invariance of the unchanged original germ fibers. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
universe u v
namespace MotivicTest.OriginalGermEtalePullback
variable {S : Scheme.{u}} [IsAffine S] {X Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
  (f : X ⟶ Y) [Etale f.left] (x : X.left) [IsIso (f.left.residueFieldMap x)]

/-- Arbitrary presheaves, not only sheaves, have the stated étale invariance. -/
theorem original_pullback_isIso : IsIso (SmoothSite.originalGermPullback F f x) :=
  inferInstance

/-- The isomorphism's forward map is exactly the existing colimit map. -/
theorem forward_map_unchanged : (SmoothSite.originalGermEtaleIso F f x).hom =
    SmoothSite.originalGermPullback F f x := rfl

/-- The explicit inverse cancels the original pullback on the target fiber. -/
theorem inverse_after_pullback (a : (SmoothSite.nisnevichPointFiberCocone Y (f.left x) F).pt) :
    SmoothSite.originalGermEtaleInverse F f x (SmoothSite.originalGermPullback F f x a) = a :=
  ConcreteCategory.congr_hom (SmoothSite.originalGermPullback_etaleInverse F f x) a

/-- The explicit inverse also cancels on the unchanged source fiber. -/
theorem pullback_after_inverse (a : (SmoothSite.nisnevichPointFiberCocone X x F).pt) :
    SmoothSite.originalGermPullback F f x (SmoothSite.originalGermEtaleInverse F f x a) = a :=
  ConcreteCategory.congr_hom (SmoothSite.originalGermEtaleInverse_pullback F f x) a

/-- The explicit inverse sends the germ of a restricted section back to its
original target germ, without assuming that sections satisfy descent. -/
theorem inverse_restricted_section (s : F.obj (op Y)) :
    SmoothSite.originalGermEtaleInverse F f x
        (SmoothSite.sectionToNisnevichPoint F X x (F.map f.op s)) =
      SmoothSite.sectionToNisnevichPoint F Y (f.left x) s := by
  have h := ConcreteCategory.congr_hom
    (SmoothSite.sectionToNisnevichPoint_originalGermPullback F f x) s
  change SmoothSite.originalGermPullback F f x
      (SmoothSite.sectionToNisnevichPoint F Y (f.left x) s) =
    SmoothSite.sectionToNisnevichPoint F X x (F.map f.op s) at h
  rw [← h]
  exact inverse_after_pullback F f x _

open Lean in
run_cmd do
  for name in #[``original_pullback_isIso, ``forward_map_unchanged,
      ``inverse_after_pullback, ``pullback_after_inverse, ``inverse_restricted_section,
      ``SmoothSite.NisnevichNeighborhood.composePullbackToTarget,
      ``SmoothSite.NisnevichNeighborhood.toPullbackCompose,
      ``SmoothSite.originalGermEtaleIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original germ étale invariance and explicit inverse: standard foundations only."

end MotivicTest.OriginalGermEtalePullback
