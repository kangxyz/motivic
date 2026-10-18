/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafBoundaryCokernel
public import Motivic.Cohomology.A1.PointedBaseOrdinaryVanishing
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleInjectives
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Original boundary germs and actual higher open-image fibers

The original quotient is formed before sheafification. At a point where its
ambient presheaf germ vanishes, its literal projection is an isomorphism on
fibers. For positive ordinary cohomology, local effacement supplies this zero
and the original big/small comparison identifies the result with the genuine
higher direct image. No global recollement or derived continuity is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
section Presheaf
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y : SmoothSite B} (j : U ⟶ Y) (Φ : (nisnevichTopology Y.left).Point.{u + 1})

local instance : (Φ.presheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A zero ambient germ makes the actual original quotient projection invertible
at the point. Sheafification is applied only after taking this quotient. -/
theorem presheafBoundaryProjection_point_isIso
    (hzero : IsZero (Φ.presheafFiber.obj ((toSmoothSite Y).op ⋙ P))) :
    IsIso (Φ.presheafFiber.map (presheafBoundaryProjection P j)) := by
  let r := presheafBoundaryRestriction P j
  have hr : Φ.presheafFiber.map r = 0 := hzero.eq_of_src _ _
  let : IsIso (cokernel.π (Φ.presheafFiber.map r)) := cokernel.π_of_zero hr
  let : IsIso (Φ.presheafFiber.map (cokernel.π r)) :=
    IsIso.of_isIso_fac_right (PreservesCokernel.π_iso_hom Φ.presheafFiber r)
  change IsIso (Φ.presheafFiber.map
    (cokernel.π r ≫ toSheafify (nisnevichTopology Y.left) (presheafNeighborhoodQuotient P j)))
  let : IsIso (Φ.presheafFiber.map
      (toSheafify (nisnevichTopology Y.left) (presheafNeighborhoodQuotient P j))) :=
    Φ.W_isInvertedBy_presheafFiber _
      ((nisnevichTopology Y.left).W_toSheafify (presheafNeighborhoodQuotient P j))
  rw [Functor.map_comp]
  infer_instance

/-- The genuine ambient boundary point fiber is the original punctured germ. -/
def presheafBoundaryPointPunctureIso
    (hzero : IsZero (Φ.presheafFiber.obj ((toSmoothSite Y).op ⋙ P))) :
    Φ.sheafFiber.obj (presheafBoundaryAmbient P j) ≅
      Φ.presheafFiber.obj ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P) := by
  let := presheafBoundaryProjection_point_isIso P j Φ hzero
  exact (asIso (Φ.presheafFiber.map (presheafBoundaryProjection P j))).symm

/-- The comparison is pinned by the original quotient projection itself. -/
@[reassoc (attr := simp)]
theorem presheafBoundaryProjection_point_comparison
    (hzero : IsZero (Φ.presheafFiber.obj ((toSmoothSite Y).op ⋙ P))) :
    Φ.presheafFiber.map (presheafBoundaryProjection P j) ≫
      (presheafBoundaryPointPunctureIso P j Φ hzero).hom = 𝟙 _ := by
  let := presheafBoundaryProjection_point_isIso P j Φ hzero
  exact (asIso (Φ.presheafFiber.map (presheafBoundaryProjection P j))).hom_inv_id

end Presheaf
section Ordinary
variable (R : CommRingCat.{u}) {U Y : SmoothSite (Spec R)} (j : U ⟶ Y)
  (Φ : (nisnevichTopology Y.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]

local instance (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The big/small ordinary comparison on the unchanged original point index. -/
def pointedPunctureOrdinaryIso (n : ℕ) :
    ((Functor.Elements.π Φ.fiber).op ⋙ (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙
      SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) ≅
    ordinaryPointCohomologyDiagram j.left Φ
      (F := (restrict U AddCommGrpCat).obj F) n :=
  NatIso.ofComponents (fun V =>
    (cohomologyRestrictionEquiv U F n ((baseChange j.left).obj V.unop.obj)).toAddCommGrpIso)
    (by
      intro V W f
      ext x
      exact cohomologyRestrictionEquiv_restriction F n
        ((baseChange j.left).map ((Functor.Elements.π Φ.fiber).map f.unop)) x)

/-- Original punctured cohomology computes the genuine higher-image point fiber. -/
def pointedPunctureColimitFiberIso (n : ℕ) :
    Φ.presheafFiber.obj ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙
      SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) ≅
    Φ.sheafFiber.obj (((directImage j.left).rightDerived n).obj
      ((restrict U AddCommGrpCat).obj F)) :=
  colim.mapIso (pointedPunctureOrdinaryIso R j Φ F n) ≪≫
    (derivedDirectImagePointOrdinaryColimitIso j.left Φ
      (injectiveResolution ((restrict U AddCommGrpCat).obj F)) n).symm

/-- Positive original-cohomology boundary germs are exactly the genuine higher
open-image fibers. This requires no HI, purity, or open-image vanishing premise. -/
def positiveBoundaryPointHigherImageIso (n : ℕ) :
    Φ.sheafFiber.obj (presheafBoundaryAmbient
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)) j) ≅
    Φ.sheafFiber.obj (((directImage j.left).rightDerived (n + 1)).obj
      ((restrict U AddCommGrpCat).obj F)) :=
  presheafBoundaryPointPunctureIso _ j Φ
    (pointedBaseColimit_isZero_succ R Y Φ F n) ≪≫
      pointedPunctureColimitFiberIso R j Φ F (n + 1)

/-- On every original punctured germ, the quotient-to-higher-image comparison
is the existing original ordinary-cohomology point-colimit comparison. -/
@[reassoc]
theorem positiveBoundaryPointHigherImageIso_projection (n : ℕ) :
    Φ.presheafFiber.map (presheafBoundaryProjection
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)) j) ≫
      (positiveBoundaryPointHigherImageIso R j Φ F n).hom =
    (pointedPunctureColimitFiberIso R j Φ F (n + 1)).hom := by
  dsimp only [positiveBoundaryPointHigherImageIso, Iso.trans_hom]
  simp only [presheafBoundaryProjection_point_comparison_assoc]

end Ordinary
end Motivic.FiniteEtaleSite
