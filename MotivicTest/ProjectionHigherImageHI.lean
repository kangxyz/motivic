/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ProjectionHigherImageHI
import Lean

/-! # Actual positive projection images and all-test-object point detection -/

public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteEtaleSite
universe u

/-- The consumer retains the actual small-site higher direct image and original HI premise. -/
theorem actual_projection_higher_image_zero
    (k : Type u) [Field k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (h : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left) AddCommGrpCat.{u + 1})] :
    IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
      ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
        ((SheafWithTransfers.toSheaf k).obj F))) :=
  projectionHigherImage_isZero_of_cohomology_HI k X F n h

/-- Detection covers all points on every test object, without a Noetherian premise. -/
example {S : Scheme.{u}}
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ (V : FiniteEtaleSite S) (z : V.left),
      IsZero ((markedResiduePoint V z).sheafFiber.obj G)) : IsZero G :=
  isZero_of_all_marked_residue_fibers G h

open Lean in
run_cmd do
  for name in #[``actual_projection_higher_image_zero,
      ``projectionHigherImage_isZero_of_cohomology_HI,
      ``projectionPointFiber_isZero_of_cohomology_HI,
      ``isZero_of_all_marked_residue_fibers,
      ``section_eq_zero_of_marked_residue_germs,
      ``exists_marked_zero_neighborhood] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual higher image under current-degree HI: standard foundations only."
