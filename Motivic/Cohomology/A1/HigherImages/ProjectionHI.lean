/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.HigherImages.PointFiberHI
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.PointDetection

/-! # Actual higher projection images vanish under the current-degree HI premise -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (k : Type u) [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual higher direct image sheaf is zero. The only homotopy-invariance
premise concerns this positive degree of the original ordinary cohomology PST. -/
theorem projectionHigherImage_isZero_of_cohomology_HI
    (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (h : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left) AddCommGrpCat.{u + 1})] :
    IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
      ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
        ((SheafWithTransfers.toSheaf k).obj F))) := by
  apply isZero_of_all_marked_residue_fibers
  intro V z
  exact projectionPointFiber_isZero_of_cohomology_HI k X (markedResiduePoint V z) F n h

end Motivic.FiniteEtaleSite
