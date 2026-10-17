module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodGraphIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealMixedBoundary
/-! # The original compact graph is the literal zero endpoint of the relative pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R)
  (T : LineBundle (neighborhoodSectionOpen R V r).toScheme)
  (N : LineBundle (fixedPsiAmbient R r))

lemma commonNeighborhoodGraph_rankOne :
    IsLocallyRankOne _ (Scheme.Hom.idealModule (commonNeighborhoodGraph R V r)) :=
  isLocallyRankOne_of_iso _ (commonNeighborhoodLocalGraphIdealIso R V r)
    (pullbackLineBundle (commonNeighborhoodToSectionAmbient R V r)
      (neighborhoodLocalIdeal R V r)).property

def commonNeighborhoodGraphPencilIso :
    tensorSheaf _ (Scheme.Hom.idealModule (commonNeighborhoodGraph R V r))
      (tensorSheaf _
        ((Scheme.Modules.pullback (commonNeighborhoodToSectionAmbient R V r)).obj
          (dualLineBundle _ T).val)
        ((Scheme.Modules.pullback (commonNeighborhoodToPsiAmbient R V r)).obj
          (dualLineBundle _ N).val)) ≅
    tensorSheaf _
      ((Scheme.Modules.pullback (commonNeighborhoodToSectionAmbient R V r)).obj
        (dualLineBundle _ (tensorLineBundle _ T
          (dualLineBundle _ (neighborhoodLocalIdeal R V r)))).val)
      ((Scheme.Modules.pullback (commonNeighborhoodToPsiAmbient R V r)).obj
        (dualLineBundle _ N).val) :=
  tensorSheafIso _ (commonNeighborhoodLocalGraphIdealIso R V r).symm (Iso.refl _) ≪≫
    mixedPulledDualTwistedIdealProductIso (commonNeighborhoodToSectionAmbient R V r)
      (commonNeighborhoodToPsiAmbient R V r) (neighborhoodLocalIdeal R V r) T N

lemma commonNeighborhoodGraphPencilIso_start
    (b : SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ N.val) :
    (commonNeighborhoodGraphPencilIso R V r T N).hom ≫
      Scheme.Modules.Hom.productSection
        (Scheme.Modules.Hom.pullbackToUnit
          (sectionDualFunctional _ (tensorLineBundle _ T
            (dualLineBundle _ (neighborhoodLocalIdeal R V r)))
            (twistedIdealSection _ (neighborhoodLocalIdeal R V r) T
              (neighborhoodLocalGraphFunctional R V r) b))
          (commonNeighborhoodToSectionAmbient R V r))
        (Scheme.Modules.Hom.pullbackToUnit (sectionDualFunctional _ N d)
          (commonNeighborhoodToPsiAmbient R V r)) =
    Scheme.Modules.Hom.productSection (Scheme.Hom.idealInclusion (commonNeighborhoodGraph R V r))
      (Scheme.Modules.Hom.productSection
        (Scheme.Modules.Hom.pullbackToUnit (sectionDualFunctional _ T b)
          (commonNeighborhoodToSectionAmbient R V r))
        (Scheme.Modules.Hom.pullbackToUnit (sectionDualFunctional _ N d)
          (commonNeighborhoodToPsiAmbient R V r))) := by
  simp only [commonNeighborhoodGraphPencilIso, Iso.trans_hom, Category.assoc]
  rw [mixedPulledDualTwistedIdealProductIso_section, tensorSheafIso_productSection]
  simp only [Iso.refl_hom, Category.id_comp]
  rw [← commonNeighborhoodLocalGraphIdealIso_inclusion R V r]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
end AlgebraicGeometry.RelativeProjectiveLine
