/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCylinderOrdinaryComparison
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Actual iterated puncture/cylinder base change on the existing point diagram -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})

/-- Total base change along the punctured cylinder is the actual iterated puncture/cylinder. -/
def punctureCylinderBaseChangeNatIso :
    baseChange ((SmoothSite.a1Projection R U).left ≫ j.left) ⋙
      toSmoothSite (SmoothSite.a1Cylinder R U) ≅
        baseChange j.left ⋙ toSmoothSite U ⋙
          SmoothSite.parameterProduct (SmoothSite.affineLine R) :=
  Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp
    (P := etaleSeparatedFiniteType) (Q := ⊤)
      (SmoothSite.a1Projection R U).left j.left) _ ≪≫
    Functor.isoWhiskerLeft (baseChange j.left) (a1BaseChangeNatIso R U)

variable (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder R U).left) AddCommGrpCat.{u + 1})]

/-- The original big/small comparison on the actual total punctured-cylinder pullback. -/
def pointedPunctureBaseChangeOrdinaryIso (n : ℕ) :
    ((Functor.Elements.π Φ.fiber ⋙
      baseChange ((SmoothSite.a1Projection R U).left ≫ j.left) ⋙
        toSmoothSite (SmoothSite.a1Cylinder R U)).op ⋙
          SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
            (SmoothSite.nisnevichTopology (Spec R)) F n) ≅
      ordinaryPointCohomologyDiagram ((SmoothSite.a1Projection R U).left ≫ j.left) Φ
        (F := (restrict (SmoothSite.a1Cylinder R U) AddCommGrpCat).obj F) n :=
  NatIso.ofComponents (fun V =>
    (cohomologyRestrictionEquiv (SmoothSite.a1Cylinder R U) F n
      ((baseChange ((SmoothSite.a1Projection R U).left ≫ j.left)).obj
        V.unop.obj)).toAddCommGrpIso) (by
    intro V W f
    ext x
    exact cohomologyRestrictionEquiv_restriction F n
      ((baseChange ((SmoothSite.a1Projection R U).left ≫ j.left)).map
        ((Functor.Elements.π Φ.fiber).map f.unop)) x)

/-- The literal puncture-cylinder diagram is the existing ordinary point cohomology diagram. -/
def pointedPunctureCylinderOrdinaryIso (n : ℕ) :
    pointedCylinderValues R Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) (pointedPuncture R j Φ) ≅
      ordinaryPointCohomologyDiagram ((SmoothSite.a1Projection R U).left ≫ j.left) Φ
        (F := (restrict (SmoothSite.a1Cylinder R U) AddCommGrpCat).obj F) n :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Functor.Elements.π Φ.fiber)
    (punctureCylinderBaseChangeNatIso R j))) _ ≪≫
      pointedPunctureBaseChangeOrdinaryIso R j Φ F n

/-- The actual punctured-cylinder germ is the actual total higher-direct-image point fiber. -/
def pointedPunctureCylinderColimitFiberIso (n : ℕ) :
    colimit (pointedCylinderValues R Φ
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) (pointedPuncture R j Φ)) ≅
      Φ.sheafFiber.obj
        (((directImage ((SmoothSite.a1Projection R U).left ≫ j.left)).rightDerived n).obj
          ((restrict (SmoothSite.a1Cylinder R U) AddCommGrpCat).obj F)) :=
  colim.mapIso (pointedPunctureCylinderOrdinaryIso R j Φ F n) ≪≫
    (derivedDirectImagePointOrdinaryColimitIso
      ((SmoothSite.a1Projection R U).left ≫ j.left) Φ
        (injectiveResolution ((restrict (SmoothSite.a1Cylinder R U) AddCommGrpCat).obj F)) n).symm

end Motivic.FiniteEtaleSite
