/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafBoundaryEtaleLocalization
public import Motivic.Cohomology.A1.BoundaryEtalePullback
public import Motivic.Cohomology.A1.PresheafBoundaryCokernel
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Étale excision for the boundary of an original presheaf

The order is original punctured sections, objectwise quotient, small ordinary
sheafification, and genuine closed inverse image. No sheaf or homotopy-invariance
premise on the original presheaf is needed for this Cartesian comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}}
  (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y U' Y' : SmoothSite B}
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] [IsSeparated p.left] [QuasiCompact p.left]
  (hpb : IsPullback q j' j p)

/-- Original ambient sections are unchanged by étale postcomposition. -/
def presheafEtaleCoefficientIso :
    (etalePostcompose p.left).op ⋙ (toSmoothSite Y).op ⋙ P ≅
      (toSmoothSite Y').op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (etaleToSmoothIso p).symm) P

/-- Original punctured sections compare through the actual Cartesian scheme isomorphism. -/
def presheafEtalePuncturedCoefficientIso :
    (etalePostcompose p.left).op ⋙ (baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P ≅
      (baseChange j'.left).op ⋙ (toSmoothSite U').op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (etalePuncturedToSmoothIso j p j' q hpb)) P

/-- The Cartesian comparison commutes with restriction before any sheafification. -/
theorem presheafEtaleCoefficient_restriction :
    Functor.whiskerLeft (etalePostcompose p.left).op (presheafBoundaryRestriction P j) ≫
        (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom =
      (presheafEtaleCoefficientIso P p).hom ≫ presheafBoundaryRestriction P j' := by
  apply NatTrans.ext
  funext V
  change P.map ((restrictionProjection j).app
      ((etalePostcompose p.left).obj V.unop)).op ≫
      P.map ((etalePuncturedToSmoothIso j p j' q hpb).hom.app V.unop).op =
    P.map ((etaleToSmoothIso p).inv.app V.unop).op ≫
      P.map ((restrictionProjection j').app V.unop).op
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change (puncturedNeighborhoodIso j p j' q hpb V.unop).hom ≫
      pullback.fst (V.unop.hom ≫ p.left) j.left =
    pullback.fst V.unop.hom j'.left ≫ 𝟙 V.unop.left
  rw [puncturedNeighborhoodIso_hom_fst]
  exact (Category.comp_id _).symm

/-- Excision of the actual objectwise quotient, before sheafification. -/
def presheafNeighborhoodQuotientEtaleIso :
    (etalePostcompose p.left).op ⋙ presheafNeighborhoodQuotient P j ≅
      presheafNeighborhoodQuotient P j' :=
  PreservesCokernel.iso ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (etalePostcompose p.left).op) (presheafBoundaryRestriction P j) ≪≫
    cokernel.mapIso _ _ (presheafEtaleCoefficientIso P p)
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb)
      (presheafEtaleCoefficient_restriction P j p j' q hpb)

@[reassoc (attr := simp)]
theorem presheafNeighborhoodQuotientEtaleIso_π :
    Functor.whiskerLeft (etalePostcompose p.left).op
        (cokernel.π (presheafBoundaryRestriction P j)) ≫
        (presheafNeighborhoodQuotientEtaleIso P j p j' q hpb).hom =
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom ≫
        cokernel.π (presheafBoundaryRestriction P j') := by
  change ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
      (etalePostcompose p.left).op).map (cokernel.π (presheafBoundaryRestriction P j)) ≫
      (presheafNeighborhoodQuotientEtaleIso P j p j' q hpb).hom = _
  simp only [presheafNeighborhoodQuotientEtaleIso, Iso.trans_hom,
    PreservesCokernel.π_iso_hom_assoc, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]

/-- Étale excision of the small sheafification of the original section quotient. -/
def presheafBoundaryAmbientEtaleIso :
    (etaleRestriction p.left).obj (presheafBoundaryAmbient P j) ≅
      presheafBoundaryAmbient P j' :=
  etaleSheafificationIso p.left (presheafNeighborhoodQuotient P j) ≪≫
    (presheafToSheaf (nisnevichTopology Y'.left) AddCommGrpCat.{u + 1}).mapIso
      (presheafNeighborhoodQuotientEtaleIso P j p j' q hpb)

/-- Every original punctured representative is preserved through quotient and unit. -/
@[reassoc (attr := simp)]
theorem presheafBoundaryAmbientEtaleIso_projection :
    Functor.whiskerLeft (etalePostcompose p.left).op (presheafBoundaryProjection P j) ≫
        (presheafBoundaryAmbientEtaleIso P j p j' q hpb).hom.hom =
      (presheafEtalePuncturedCoefficientIso P j p j' q hpb).hom ≫
        presheafBoundaryProjection P j' := by
  simp only [presheafBoundaryProjection, presheafBoundaryAmbientEtaleIso,
    Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerLeft_comp, Category.assoc]
  dsimp only [presheafBoundaryAmbient, presheafNeighborhoodQuotient]
  rw [etaleSheafificationIso_unit_assoc]
  rw [← toSheafify_naturality, ← Category.assoc,
    presheafNeighborhoodQuotientEtaleIso_π]
  simp only [Category.assoc]

/-- Apply genuine closed inverse image after the ambient étale excision comparison. -/
def presheafBoundaryEtaleExcisionIso {Z : SmoothSite B} (i' : Z ⟶ Y') :
    presheafBoundary P j (i' ≫ p) ≅ presheafBoundary P j' i' :=
  ((inverseImageCompIso i'.left p.left).app (presheafBoundaryAmbient P j)).symm ≪≫
    (inverseImage i'.left).mapIso
      ((inverseImageEtaleIso p.left).app (presheafBoundaryAmbient P j)) ≪≫
    (inverseImage i'.left).mapIso (presheafBoundaryAmbientEtaleIso P j p j' q hpb)

include hpb in
/-- Boundary vanishing on an actual étale chart transfers along its specified closed lift. -/
theorem isZero_presheafBoundary_of_etale {Z : SmoothSite B} (i' : Z ⟶ Y')
    (h : IsZero (presheafBoundary P j' i')) :
    IsZero (presheafBoundary P j (i' ≫ p)) :=
  h.of_iso (presheafBoundaryEtaleExcisionIso P j p j' q hpb i')

end Motivic.FiniteEtaleSite
