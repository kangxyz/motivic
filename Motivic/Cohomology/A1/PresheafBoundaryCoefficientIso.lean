/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafBoundaryCokernel

/-! # Original boundary quotients respect coefficient isomorphisms

The comparison is induced before sheafification by the specified natural
isomorphism of original presheaves. It preserves the quotient projection and
canonical sheafification unit.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {B : Scheme.{u}} {P Q : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
  (e : P ≅ Q) {U Y : SmoothSite B} (j : U ⟶ Y)

/-- The specified coefficient comparison preserves actual puncture restriction. -/
theorem presheafBoundaryRestriction_coefficientIso :
    presheafBoundaryRestriction P j ≫
        Functor.whiskerLeft ((baseChange j.left).op ⋙ (toSmoothSite U).op) e.hom =
      Functor.whiskerLeft (toSmoothSite Y).op e.hom ≫ presheafBoundaryRestriction Q j := by
  apply NatTrans.ext
  funext V
  exact e.hom.naturality ((restrictionProjection j).app V.unop).op

/-- The actual original objectwise cokernels compare by the coefficient isomorphism. -/
def presheafNeighborhoodQuotientCoefficientIso :
    presheafNeighborhoodQuotient P j ≅ presheafNeighborhoodQuotient Q j :=
  cokernel.mapIso _ _ (Functor.isoWhiskerLeft (toSmoothSite Y).op e)
    (Functor.isoWhiskerLeft ((baseChange j.left).op ⋙ (toSmoothSite U).op) e)
    (presheafBoundaryRestriction_coefficientIso e j)

/-- The cokernel comparison retains each original punctured representative. -/
@[reassoc (attr := simp)]
theorem presheafNeighborhoodQuotientCoefficientIso_π :
    cokernel.π (presheafBoundaryRestriction P j) ≫
        (presheafNeighborhoodQuotientCoefficientIso e j).hom =
      Functor.whiskerLeft ((baseChange j.left).op ⋙ (toSmoothSite U).op) e.hom ≫
        cokernel.π (presheafBoundaryRestriction Q j) := by
  simp [presheafNeighborhoodQuotientCoefficientIso]

/-- Only after the original quotient do we apply small ordinary sheafification. -/
def presheafBoundaryAmbientCoefficientIso :
    presheafBoundaryAmbient P j ≅ presheafBoundaryAmbient Q j :=
  (presheafToSheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1}).mapIso
    (presheafNeighborhoodQuotientCoefficientIso e j)

/-- Original quotient projections and canonical sheafification units commute
with the specified coefficient comparison. -/
@[reassoc (attr := simp)]
theorem presheafBoundaryAmbientCoefficientIso_projection :
    presheafBoundaryProjection P j ≫ (presheafBoundaryAmbientCoefficientIso e j).hom.hom =
      Functor.whiskerLeft ((baseChange j.left).op ⋙ (toSmoothSite U).op) e.hom ≫
        presheafBoundaryProjection Q j := by
  simp only [presheafBoundaryProjection, presheafBoundaryAmbientCoefficientIso,
    Functor.mapIso_hom, Category.assoc]
  dsimp only [presheafBoundaryAmbient, presheafNeighborhoodQuotient]
  rw [← toSheafify_naturality, ← Category.assoc,
    presheafNeighborhoodQuotientCoefficientIso_π]
  simp only [Category.assoc]

end Motivic.FiniteEtaleSite
