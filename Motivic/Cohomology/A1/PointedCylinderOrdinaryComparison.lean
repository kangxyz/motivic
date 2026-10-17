/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PuncturePointDiagrams
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleA1BaseChangeNaturality
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapAtBase

/-! # The pointed cylinder diagram computes the existing genuine higher-image point fiber -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder R X).left) AddCommGrpCat.{u + 1})]

/-- The original big/small comparison is natural on the exact existing point-neighborhood index. -/
def pointedCylinderBaseChangeOrdinaryIso (n : ℕ) :
    ((Functor.Elements.π Φ.fiber ⋙ baseChange (SmoothSite.a1Projection R X).left ⋙
      toSmoothSite (SmoothSite.a1Cylinder R X)).op ⋙
        SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec R)) F n) ≅
    ordinaryPointCohomologyDiagram (SmoothSite.a1Projection R X).left Φ
      (F := (restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F) n :=
  NatIso.ofComponents (fun V =>
    (cohomologyRestrictionEquiv (SmoothSite.a1Cylinder R X) F n
      ((baseChange (SmoothSite.a1Projection R X).left).obj V.unop.obj)).toAddCommGrpIso) (by
    intro V W f
    ext x
    exact cohomologyRestrictionEquiv_restriction F n
      ((baseChange (SmoothSite.a1Projection R X).left).map
        ((Functor.Elements.π Φ.fiber).map f.unop)) x)

/-- Geometric base change identifies cylinder cohomology with the existing diagram. -/
def pointedCylinderOrdinaryIso (n : ℕ) :
    pointedCylinderValues R Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) (pointedBase R Φ) ≅
      ordinaryPointCohomologyDiagram (SmoothSite.a1Projection R X).left Φ
        (F := (restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F) n :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Functor.Elements.π Φ.fiber)
    (a1BaseChangeNatIso R X))) _ ≪≫ pointedCylinderBaseChangeOrdinaryIso R X Φ F n

/-- The actual cylinder germ is the actual higher-direct-image point fiber, with no new index. -/
def pointedCylinderColimitFiberIso (n : ℕ) :
    colimit (pointedCylinderValues R Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) (pointedBase R Φ)) ≅
      Φ.sheafFiber.obj (((directImage (SmoothSite.a1Projection R X).left).rightDerived n).obj
        ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F)) :=
  colim.mapIso (pointedCylinderOrdinaryIso R X Φ F n) ≪≫
    (derivedDirectImagePointOrdinaryColimitIso (SmoothSite.a1Projection R X).left Φ
      (injectiveResolution ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat).obj F)) n).symm

end Motivic.FiniteEtaleSite
