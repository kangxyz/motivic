/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedBaseOrdinaryVanishing
public import Motivic.Transfers.SheafCohomologyWithTransfers

/-! # Current-degree homotopy invariance kills actual projection point fibers -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable (k : Type u) [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Only the explicitly specified positive degree is assumed homotopy invariant. -/
theorem projectionPointFiber_isZero_of_cohomology_HI
    (X : SmoothSite (Spec (.of k)))
    (Φ : (nisnevichTopology X.left).Point.{u + 1})
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (h : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
    [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left) AddCommGrpCat.{u + 1})] :
    IsZero (Φ.sheafFiber.obj
      (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) := by
  let A := (SheafWithTransfers.toSheaf k).obj F
  let P := SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) A (n + 1)
  have hi (Y : SmoothSite (Spec (.of k))) :
      IsIso (A1.projectionPullback (.of k) P Y) :=
    (NatIso.isIso_map_iff (SheafCohomology.withTransfersGraphIso k F (n + 1))
      (SmoothSite.a1Projection (.of k) Y).op).mp (h Y)
  have happ (V : Φ.fiber.Elementsᵒᵖ) :
      IsIso ((pointedProjection (.of k) Φ P (pointedBase (.of k) Φ)).app V) :=
    hi _
  let : IsIso (pointedProjection (.of k) Φ P (pointedBase (.of k) Φ)) :=
    NatIso.isIso_of_isIso_app _
  have hz := pointedBaseColimit_isZero_succ (.of k) X Φ A n
  have hc : IsZero (colimit (pointedCylinderValues (.of k) Φ P
      (pointedBase (.of k) Φ))) :=
    hz.of_iso (colim.mapIso (asIso
      (pointedProjection (.of k) Φ P (pointedBase (.of k) Φ)))).symm
  exact hc.of_iso (pointedCylinderColimitFiberIso (.of k) X Φ A (n + 1)).symm

end Motivic.FiniteEtaleSite
