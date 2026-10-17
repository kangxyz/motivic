/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointOrdinaryColimit
public import Motivic.AlgebraicGeometry.SmoothSiteParameterProducts
public import Motivic.Cohomology.A1.Basic

/-! # Original projection and zero-section maps on actual pointed puncture diagrams

The index is exactly the point-neighborhood category used by ordinaryPointCohomologyDiagram.
No global dimension drop on a finite-stage puncture is asserted.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The original smooth neighborhood diagram on the existing point index. -/
def pointedBase : Φ.fiber.Elements ⥤ SmoothSite (Spec R) :=
  Functor.Elements.π Φ.fiber ⋙ toSmoothSite X

/-- The actual puncture of every existing point neighborhood, by geometric base change. -/
def pointedPuncture : Φ.fiber.Elements ⥤ SmoothSite (Spec R) :=
  Functor.Elements.π Φ.fiber ⋙ baseChange j.left ⋙ toSmoothSite U

/-- The literal inclusions of pulled-back punctured neighborhoods. -/
def pointedPunctureInclusion : pointedPuncture R j Φ ⟶ pointedBase R Φ :=
  Functor.whiskerLeft (Functor.Elements.π Φ.fiber) (restrictionProjection j)

/-- Original presheaf values on the actual base neighborhoods. -/
def pointedBaseValues : Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (pointedBase R Φ).op ⋙ P

/-- Original presheaf values on the actual punctured neighborhoods. -/
def pointedPunctureValues : Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (pointedPuncture R j Φ).op ⋙ P

/-- Actual original restrictions to the puncture on the same index. -/
def pointedRestriction : pointedBaseValues R Φ P ⟶ pointedPunctureValues R j Φ P :=
  Functor.whiskerRight (NatTrans.op (pointedPunctureInclusion R j Φ)) P

/-- The original cylinder values, on the same pointed-neighborhood index. -/
def pointedCylinderValues (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (G ⋙ SmoothSite.parameterProduct (SmoothSite.affineLine R)).op ⋙ P

/-- Projection pullback is the literal original projection on every neighborhood. -/
def pointedProjection (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    G.op ⋙ P ⟶ pointedCylinderValues R Φ P G where
  app V := A1.projectionPullback R P (G.obj V.unop)
  naturality _ _ f := A1.projectionPullback_naturality R P (G.map f.unop)

/-- Zero-section restriction is the literal original section on every neighborhood. -/
def pointedZeroSection (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    pointedCylinderValues R Φ P G ⟶ G.op ⋙ P where
  app V := A1.sectionPullback R P (G.obj V.unop) 0
  naturality V W f := by
    change P.map (SmoothSite.a1Map R (G.map f.unop)).op ≫
      P.map (SmoothSite.a1Section R (G.obj W.unop) 0).op =
        P.map (SmoothSite.a1Section R (G.obj V.unop) 0).op ≫ P.map (G.map f.unop).op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      SmoothSite.a1Section_naturality]

/-- The actual original cylinder restriction induced by the puncture inclusion. -/
def pointedCylinderRestriction :
    pointedCylinderValues R Φ P (pointedBase R Φ) ⟶
      pointedCylinderValues R Φ P (pointedPuncture R j Φ) :=
  Functor.whiskerRight (NatTrans.op (Functor.whiskerRight
    (pointedPunctureInclusion R j Φ) (SmoothSite.parameterProduct (SmoothSite.affineLine R)))) P

/-- The original zero section is a retraction of the original projection on the whole diagram. -/
theorem pointedProjection_zeroSection (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    pointedProjection R Φ P G ≫ pointedZeroSection R Φ P G = 𝟙 _ := by
  apply NatTrans.ext
  funext V
  exact A1.projectionPullback_sectionPullback R P (G.obj V.unop) 0

/-- Actual zero-section restriction commutes with actual puncture restriction. -/
theorem pointedCylinderRestriction_zeroSection :
    pointedCylinderRestriction R j Φ P ≫ pointedZeroSection R Φ P (pointedPuncture R j Φ) =
      pointedZeroSection R Φ P (pointedBase R Φ) ≫ pointedRestriction R j Φ P := by
  apply NatTrans.ext
  funext V
  change P.map (SmoothSite.a1Map R ((pointedPunctureInclusion R j Φ).app V.unop)).op ≫
    P.map (SmoothSite.a1Section R ((pointedPuncture R j Φ).obj V.unop) 0).op =
      P.map (SmoothSite.a1Section R ((pointedBase R Φ).obj V.unop) 0).op ≫
        P.map ((pointedPunctureInclusion R j Φ).app V.unop).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    SmoothSite.a1Section_naturality]

end Motivic.FiniteEtaleSite
