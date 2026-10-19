module

public import Motivic.Cohomology.A1.Boundary.Etale.Pullback

/-! # Étale excision for the actual boundary cokernel sheaf

The proof uses actual étale-site localization and Cartesian punctured neighborhoods.
It does not assert excision for global section cokernels or use homotopy invariance.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} {U Y U' Y' : SmoothSite B}
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
  (j : U ⟶ Y) (p : Y' ⟶ Y) (j' : U' ⟶ Y') (q : U' ⟶ U)
  [Etale p.left] [IsSeparated p.left] [QuasiCompact p.left]
  (hpb : IsPullback q j' j p)

/-- The original coefficient sheaf restricts literally to the étale source. -/
def etaleCoefficientIso :
    (etaleRestriction p.left).obj ((restrict Y AddCommGrpCat).obj F) ≅
      (restrict Y' AddCommGrpCat).obj F :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (NatIso.op (etaleToSmoothIso p).symm) F.obj)

/-- Actual punctured sections commute with restriction to an étale neighborhood. -/
def etalePuncturedCoefficientIso :
    (etaleRestriction p.left).obj
      ((directImage j.left).obj ((restrict U AddCommGrpCat).obj F)) ≅
    (directImage j'.left).obj ((restrict U' AddCommGrpCat).obj F) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (NatIso.op (etalePuncturedToSmoothIso j p j' q hpb)) F.obj)

/-- The two actual restriction maps commute with the Cartesian comparisons. -/
theorem etaleCoefficient_restriction :
    (etaleRestriction p.left).map (restrictionToDirectImage F j) ≫
        (etalePuncturedCoefficientIso F j p j' q hpb).hom =
      (etaleCoefficientIso F p).hom ≫ restrictionToDirectImage F j' := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  change F.obj.map ((restrictionProjection j).app
      ((etalePostcompose p.left).obj V.unop)).op ≫
      F.obj.map ((etalePuncturedToSmoothIso j p j' q hpb).hom.app V.unop).op =
    F.obj.map ((etaleToSmoothIso p).inv.app V.unop).op ≫
      F.obj.map ((restrictionProjection j').app V.unop).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change (puncturedNeighborhoodIso j p j' q hpb V.unop).hom ≫
      pullback.fst (V.unop.hom ≫ p.left) j.left =
    pullback.fst V.unop.hom j'.left ≫ 𝟙 V.unop.left
  rw [puncturedNeighborhoodIso_hom_fst]
  exact (Category.comp_id _).symm

/-- Étale restriction preserves the actual ambient sheaf cokernel of restriction. -/
def boundaryAmbientEtaleIso :
    (etaleRestriction p.left).obj (boundaryAmbientCokernel F j) ≅
      boundaryAmbientCokernel F j' :=
  PreservesCokernel.iso (etaleRestriction p.left) (restrictionToDirectImage F j) ≪≫
    cokernel.mapIso _ _ (etaleCoefficientIso F p)
      (etalePuncturedCoefficientIso F j p j' q hpb)
      (etaleCoefficient_restriction F j p j' q hpb)

/-- The excision comparison sends the original ambient quotient representative
by the literal Cartesian restriction on punctured sections. -/
@[reassoc (attr := simp)]
theorem boundaryAmbientEtaleIso_π :
    (etaleRestriction p.left).map (cokernel.π (restrictionToDirectImage F j)) ≫
        (boundaryAmbientEtaleIso F j p j' q hpb).hom =
      (etalePuncturedCoefficientIso F j p j' q hpb).hom ≫
        cokernel.π (restrictionToDirectImage F j') := by
  simp [boundaryAmbientEtaleIso]

/-- Genuine boundary-sheaf excision along an étale Cartesian square, retaining
any original closed source and its specified lift. No quotient-surjectivity
or cohomology-vanishing assumption occurs. -/
def boundaryEtaleExcisionIso {Z : SmoothSite B} (i' : Z ⟶ Y') :
    boundaryCokernel F j (i' ≫ p) ≅ boundaryCokernel F j' i' :=
  ((inverseImageCompIso i'.left p.left).app (boundaryAmbientCokernel F j)).symm ≪≫
    (inverseImage i'.left).mapIso
      ((inverseImageEtaleIso p.left).app (boundaryAmbientCokernel F j)) ≪≫
    (inverseImage i'.left).mapIso (boundaryAmbientEtaleIso F j p j' q hpb)

end Motivic.FiniteEtaleSite
