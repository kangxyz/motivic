/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.BoundaryEtaleLocalization
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Étale restriction commutes with small ordinary sheafification

This comparison applies to the original neighborhood quotient, not to a
sheafification of the original smooth presheaf before puncturing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {S T : Scheme.{u}} (p : T ⟶ S)
  [Etale p] [IsSeparated p] [QuasiCompact p]

/-- Étale postcomposition lifts Nisnevich covers by its actual base-change adjoint. -/
instance etalePostcompose_isCocontinuous :
    (etalePostcompose p).IsCocontinuous (nisnevichTopology T) (nisnevichTopology S) :=
  ((etalePostcomposeAdjunction p).isCocontinuous_iff_coverPreserving
    (nisnevichTopology T) (nisnevichTopology S)).mpr
    (CoverPreserving.of_isContinuous (baseChange p) _ _)

/-- Sheafify an original presheaf and then restrict, or restrict and then sheafify. -/
def etaleSheafificationIso (Q : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleRestriction p).obj
        ((presheafToSheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}).obj Q) ≅
      (presheafToSheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}).obj
        ((etalePostcompose p).op ⋙ Q) :=
  ((etalePostcompose p).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u + 1} (nisnevichTopology T) (nisnevichTopology S)).symm.app Q

/-- The comparison retains the original sheafification unit on every neighborhood. -/
@[reassoc (attr := simp)]
theorem etaleSheafificationIso_unit
    (Q : (FiniteEtaleSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Functor.whiskerLeft (etalePostcompose p).op (toSheafify (nisnevichTopology S) Q) ≫
        (etaleSheafificationIso p Q).hom.hom =
      toSheafify (nisnevichTopology T) ((etalePostcompose p).op ⋙ Q) := by
  have h := (etalePostcompose p).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u + 1} (nisnevichTopology T) (nisnevichTopology S) Q
  change Functor.whiskerLeft (etalePostcompose p).op
      (toSheafify (nisnevichTopology S) Q) ≫
      (((etalePostcompose p).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{u + 1} (nisnevichTopology T) (nisnevichTopology S)).inv.app Q).hom = _
  rw [← h, Category.assoc]
  rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
  exact Category.comp_id _

end Motivic.FiniteEtaleSite
