/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Representatives

/-! # Original signed restriction differences give genuine boundary equalities -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B} (j : U ⟶ Y) (i : Z ⟶ Y)

/-- The actual signed lift relation kills its ambient correction and preserves
restriction of the original punctured section, even when `P` is not a sheaf. -/
theorem presheafBoundaryGenerator_of_difference
    {W W' : EtaleSeparatedFiniteType Y.left} (f : W' ⟶ W)
    (s : ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P).obj (op W))
    (t : ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P).obj (op W'))
    (c : P.obj (op ((toSmoothSite Y).obj W')))
    (h : t - (presheafBoundaryRestriction P j).app (op W') c =
      ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P).map f.op s) :
    (presheafBoundaryGenerator P j i).app (op W') t =
      (presheafBoundary P j i).obj.map ((baseChange i.left).map f).op
        ((presheafBoundaryGenerator P j i).app (op W) s) := by
  have hmap := congrArg ((presheafBoundaryGenerator P j i).app (op W')) h
  rw [map_sub, presheafBoundaryGenerator_extend, sub_zero] at hmap
  exact hmap.trans (ConcreteCategory.congr_hom
    ((presheafBoundaryGenerator P j i).naturality f.op) s)

end Motivic.FiniteEtaleSite
