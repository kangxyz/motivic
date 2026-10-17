/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.PresheafBoundaryCokernel

/-! # Original punctured sections jointly detect maps out of the actual boundary -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B} (j : U ⟶ Y) (i : Z ⟶ Y)

/-- The genuine generator map uses the original quotient, sheafification and inverse-image unit. -/
def presheafBoundaryGenerator :
    (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P ⟶
      ((directImage i.left).obj (presheafBoundary P j i)).obj :=
  presheafBoundaryProjection P j ≫
    ((imageAdjunction i.left).unit.app (presheafBoundaryAmbient P j)).hom

/-- Right cancellation against original punctured-section generators suffices. This follows
from the actual inverse-image adjunction, sheafification and the original cokernel. -/
theorem presheafBoundary_hom_ext
    {G : Sheaf (nisnevichTopology Z.left) AddCommGrpCat.{u + 1}}
    {f g : presheafBoundary P j i ⟶ G}
    (h : presheafBoundaryGenerator P j i ≫ ((directImage i.left).map f).hom =
      presheafBoundaryGenerator P j i ≫ ((directImage i.left).map g).hom) : f = g := by
  apply ((imageAdjunction i.left).homEquiv _ _).injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (nisnevichTopology Y.left) _ _
    ((directImage i.left).obj G).property
  apply (cancel_epi (cokernel.π (presheafBoundaryRestriction P j))).mp
  simpa only [Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom,
    presheafBoundaryGenerator,
    presheafBoundaryProjection, Category.assoc] using h

end Motivic.FiniteEtaleSite
