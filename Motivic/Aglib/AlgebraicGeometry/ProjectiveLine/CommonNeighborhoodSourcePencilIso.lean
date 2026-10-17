module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodRetainedPencilIso
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.CommonNeighborhoodRetainedProductPullback
/-! # Original source-span factors and the actual relative compact pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme] (r : R) (l m : ℕ)

def commonNeighborhoodSourcePoleLine : LineBundle (commonNeighborhoodRetainedCurve R V r) :=
  tensorLineBundle _
    (commonNeighborhoodRetainedLambdaLine R V r (dualLineBundle _ (neighborhoodLocalTwist R V r l)))
    (commonNeighborhoodRetainedPsiLine R V r (dualLineBundle _ (fixedPsiTwistLine R r m)))

def commonNeighborhoodSourceNumeratorLine : LineBundle (commonNeighborhoodRetainedCurve R V r) :=
  tensorLineBundle _
    (commonNeighborhoodRetainedLambdaLine R V r (dualLineBundle _
      (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r)))))
    (commonNeighborhoodRetainedPsiLine R V r (dualLineBundle _ (fixedPsiTwistLine R r m)))

def commonNeighborhoodSourceGraphLine : LineBundle (commonNeighborhoodRetainedCurve R V r) :=
  tensorLineBundle _ (commonNeighborhoodRetainedGraphLine R V r)
    (commonNeighborhoodSourcePoleLine R V r l m)

def commonNeighborhoodSourceCompactIso :
    (commonNeighborhoodSourceGraphLine R V r l m).val ≅
      (pullbackLineBundle (commonNeighborhoodRetainedInclusion R V r)
        (commonNeighborhoodPencilLine R V r l m)).val :=
  tensorSheafIso _ (Iso.refl _)
    (commonNeighborhoodRetainedProductPullbackIso R V r
      (dualLineBundle _ (neighborhoodLocalTwist R V r l))
      (dualLineBundle _ (fixedPsiTwistLine R r m))) ≪≫
    commonNeighborhoodRetainedPencilIso R V r l m

def commonNeighborhoodSourcePencilIso :
    (commonNeighborhoodSourceGraphLine R V r l m).val ≅
      (commonNeighborhoodSourceNumeratorLine R V r l m).val :=
  commonNeighborhoodSourceCompactIso R V r l m ≪≫
    (commonNeighborhoodRetainedProductPullbackIso R V r
      (dualLineBundle _ (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
        (dualLineBundle _ (neighborhoodLocalIdeal R V r))))
      (dualLineBundle _ (fixedPsiTwistLine R r m))).symm

variable (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
  (e : neighborhoodFrame R V r l)

lemma NeighborhoodSectionPair.sourceCompactIso_start
    (d : NeighborhoodSectionPair R V hV r l e)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :
    (commonNeighborhoodSourceCompactIso R V r l m).hom ≫
      Scheme.Modules.Hom.pullbackToUnit (d.pencilStart R V hV r l m e t)
        (commonNeighborhoodRetainedInclusion R V r) =
    Scheme.Modules.Hom.productSection
      (Scheme.Hom.idealInclusion (commonNeighborhoodRetainedGraph R V r))
      (Scheme.Modules.Hom.productSection
        (commonNeighborhoodRetainedLambdaFunctional R V r
          (sectionDualFunctional _ (neighborhoodLocalTwist R V r l) d.normalizedDenominator))
        (commonNeighborhoodRetainedPsiFunctional R V r
          (sectionDualFunctional _ (fixedPsiTwistLine R r m) t))) := by
  simp only [commonNeighborhoodSourceCompactIso, Iso.trans_hom, Category.assoc]
  rw [d.retainedPencilIso_start R V r l m hV e t, tensorSheafIso_productSection]
  simp only [Iso.refl_hom, Category.id_comp]
  dsimp only [NeighborhoodSectionPair.poleFunctional, mixedProductFunctional]
  rw [commonNeighborhoodRetainedProductPullbackIso_functional]

lemma NeighborhoodSectionPair.sourceCompactIso_end
    (d : NeighborhoodSectionPair R V hV r l e)
    (n : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiTwistLine R r m).val) :
    (commonNeighborhoodSourceCompactIso R V r l m).hom ≫
      Scheme.Modules.Hom.pullbackToUnit (d.pencilEnd R V hV r l m e n)
        (commonNeighborhoodRetainedInclusion R V r) =
    (commonNeighborhoodSourcePencilIso R V r l m).hom ≫
      Scheme.Modules.Hom.productSection
        (commonNeighborhoodRetainedLambdaFunctional R V r
          (sectionDualFunctional _ (tensorLineBundle _ (neighborhoodLocalTwist R V r l)
            (dualLineBundle _ (neighborhoodLocalIdeal R V r))) d.normalizedNumerator))
        (commonNeighborhoodRetainedPsiFunctional R V r
          (sectionDualFunctional _ (fixedPsiTwistLine R r m) n)) := by
  simp only [commonNeighborhoodSourcePencilIso, Iso.trans_hom, Category.assoc]
  rw [← commonNeighborhoodRetainedProductPullbackIso_functional]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
  rfl
end AlgebraicGeometry.RelativeProjectiveLine
