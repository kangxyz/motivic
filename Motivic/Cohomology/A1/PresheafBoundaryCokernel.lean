/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.BoundaryCokernelSheaf

/-! # Boundary quotients of original presheaves before sheafification -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B}

/-- Restrict the original presheaf, not its associated sheaf, to punctured neighborhoods. -/
def presheafBoundaryRestriction (j : U ⟶ Y) :
    (toSmoothSite Y).op ⋙ P ⟶
      (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P :=
  Functor.whiskerRight (NatTrans.op (restrictionProjection j)) P

/-- The actual objectwise quotient of original sections. -/
def presheafNeighborhoodQuotient (j : U ⟶ Y) :=
  cokernel (presheafBoundaryRestriction P j)

/-- Sheafification occurs only after taking the original neighborhood quotient. -/
def presheafBoundaryAmbient (j : U ⟶ Y) :
    Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1}).obj
    (presheafNeighborhoodQuotient P j)

/-- Actual closed inverse image of the sheafified original quotient. -/
def presheafBoundary (j : U ⟶ Y) (i : Z ⟶ Y) :
    Sheaf (nisnevichTopology Z.left) AddCommGrpCat.{u + 1} :=
  (inverseImage i.left).obj (presheafBoundaryAmbient P j)

/-- Original punctured sections map through their quotient and its sheafification unit. -/
def presheafBoundaryProjection (j : U ⟶ Y) :
    (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P ⟶
      (presheafBoundaryAmbient P j).obj :=
  cokernel.π (presheafBoundaryRestriction P j) ≫
    toSheafify (nisnevichTopology Y.left) (presheafNeighborhoodQuotient P j)

@[reassoc (attr := simp)]
theorem presheafBoundaryRestriction_projection (j : U ⟶ Y) :
    presheafBoundaryRestriction P j ≫ presheafBoundaryProjection P j = 0 := by
  unfold presheafBoundaryProjection
  rw [← Category.assoc, cokernel.condition, zero_comp]

end Motivic.FiniteEtaleSite
