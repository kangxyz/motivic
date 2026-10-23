/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Refinement.Retained.SectionChange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.PencilComparison
/-! # Literal retained factor coefficients and the original compact product -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
private theorem commonPullbackToUnit_comp {W C Z : Scheme.{u}}
    (f : W ⟶ C) (g : C ⟶ Z) {L : Z.Modules}
    (a : L ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    Scheme.Modules.Hom.pullbackToUnit (Scheme.Modules.Hom.pullbackToUnit a g) f =
      (Scheme.Modules.pullbackComp f g).hom.app L ≫
        Scheme.Modules.Hom.pullbackToUnit a (f ≫ g) :=
  GlobalBoundaryPencil.pullback_map_comp f g a

/-- Native coefficient comparison for the two equal pullback routes used below. -/
def commonCoefficientComparisonIso {W A D C : Scheme.{u}}
    (f : W ⟶ A) (g : A ⟶ C) (j : W ⟶ D) (k : D ⟶ C)
    (h : f ≫ g = j ≫ k) (L : C.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback k).obj L) :=
  (Scheme.Modules.pullbackComp f g).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
    (Scheme.Modules.pullbackComp j k).symm.app L

private theorem commonCoefficientComparison {W A D C : Scheme.{u}}
    (f : W ⟶ A) (g : A ⟶ C) (j : W ⟶ D) (k : D ⟶ C)
    (h : f ≫ g = j ≫ k) {L : C.Modules}
    (a : L ⟶ SheafOfModules.unit C.ringCatSheaf) :
    (commonCoefficientComparisonIso f g j k h L).hom ≫
        Scheme.Modules.Hom.pullbackToUnit (Scheme.Modules.Hom.pullbackToUnit a k) j =
      Scheme.Modules.Hom.pullbackToUnit (Scheme.Modules.Hom.pullbackToUnit a g) f := by
  rw [commonPullbackToUnit_comp]
  simp only [commonCoefficientComparisonIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact (pullbackToUnit_comp_congr f g (j ≫ k) h a).symm

variable (R : Type u) [CommRing R] (V : (Spec (.of (Polynomial R))).Opens)
  [IsAffine V.toScheme] (r : R)

/-- The iterated pullback of a section-side line bundle to the retained common curve. -/
abbrev commonNeighborhoodRetainedLambdaLine
    (L : LineBundle (neighborhoodSectionOpen R V r).toScheme) :=
  pullbackLineBundle (commonNeighborhoodRetainedToSection R V r)
    (pullbackLineBundle (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r) L)

/-- The iterated pullback of a fixed Psi line bundle to the retained common curve. -/
abbrev commonNeighborhoodRetainedPsiLine (M : LineBundle (fixedPsiAmbient R r)) :=
  pullbackLineBundle (commonNeighborhoodRetainedToPsi R V r)
    (pullbackLineBundle (fixedPsiRetainedInclusion R r V) M)

/-- The iterated pullback of a section-side functional to the retained common curve. -/
abbrev commonNeighborhoodRetainedLambdaFunctional
    {L : (neighborhoodSectionOpen R V r).toScheme.Modules}
    (a : L ⟶ SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf) :=
  Scheme.Modules.Hom.pullbackToUnit
    (Scheme.Modules.Hom.pullbackToUnit a
      (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r))
    (commonNeighborhoodRetainedToSection R V r)

/-- The iterated pullback of a fixed Psi functional to the retained common curve. -/
abbrev commonNeighborhoodRetainedPsiFunctional {M : (fixedPsiAmbient R r).Modules}
    (b : M ⟶ SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf) :=
  Scheme.Modules.Hom.pullbackToUnit
    (Scheme.Modules.Hom.pullbackToUnit b (fixedPsiRetainedInclusion R r V))
    (commonNeighborhoodRetainedToPsi R V r)

/-- The comparison between the iterated section-side pullback and restriction of the ambient
pullback. -/
def commonNeighborhoodRetainedLambdaPullbackIso
    (L : LineBundle (neighborhoodSectionOpen R V r).toScheme) :
    (commonNeighborhoodRetainedLambdaLine R V r L).val ≅
      (Scheme.Modules.pullback (commonNeighborhoodRetainedInclusion R V r)).obj
        ((Scheme.Modules.pullback (commonNeighborhoodToSectionAmbient R V r)).obj L.val) :=
  commonCoefficientComparisonIso (commonNeighborhoodRetainedToSection R V r)
    (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodRetainedToSection_inclusion R V r) L.val

/-- The comparison between the iterated Psi pullback and restriction of the ambient pullback. -/
def commonNeighborhoodRetainedPsiPullbackIso (M : LineBundle (fixedPsiAmbient R r)) :
    (commonNeighborhoodRetainedPsiLine R V r M).val ≅
      (Scheme.Modules.pullback (commonNeighborhoodRetainedInclusion R V r)).obj
        ((Scheme.Modules.pullback (commonNeighborhoodToPsiAmbient R V r)).obj M.val) :=
  commonCoefficientComparisonIso (commonNeighborhoodRetainedToPsi R V r)
    (fixedPsiRetainedInclusion R r V)
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodToPsiAmbient R V r)
    (commonNeighborhoodRetainedToPsi_inclusion R V r) M.val

lemma commonNeighborhoodRetainedLambdaPullbackIso_functional
    (L : LineBundle (neighborhoodSectionOpen R V r).toScheme)
    (a : L.val ⟶ SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf) :
    (commonNeighborhoodRetainedLambdaPullbackIso R V r L).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.pullbackToUnit a (commonNeighborhoodToSectionAmbient R V r))
        (commonNeighborhoodRetainedInclusion R V r) =
      commonNeighborhoodRetainedLambdaFunctional R V r a :=
  commonCoefficientComparison (commonNeighborhoodRetainedToSection R V r)
    (neighborhoodRetainedInclusion R V ∣_ neighborhoodSectionOpen R V r)
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodToSectionAmbient R V r)
    (commonNeighborhoodRetainedToSection_inclusion R V r) a

omit [IsAffine V.toScheme] in
lemma commonNeighborhoodRetainedPsiPullbackIso_functional
    (M : LineBundle (fixedPsiAmbient R r))
    (b : M.val ⟶ SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf) :
    (commonNeighborhoodRetainedPsiPullbackIso R V r M).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.pullbackToUnit b (commonNeighborhoodToPsiAmbient R V r))
        (commonNeighborhoodRetainedInclusion R V r) =
      commonNeighborhoodRetainedPsiFunctional R V r b :=
  commonCoefficientComparison (commonNeighborhoodRetainedToPsi R V r)
    (fixedPsiRetainedInclusion R r V)
    (commonNeighborhoodRetainedInclusion R V r) (commonNeighborhoodToPsiAmbient R V r)
    (commonNeighborhoodRetainedToPsi_inclusion R V r) b

/-- Actual twice-retained product coefficients, not a replacement line or chosen frame. -/
def commonNeighborhoodRetainedProductPullbackIso
    (L : LineBundle (neighborhoodSectionOpen R V r).toScheme)
    (M : LineBundle (fixedPsiAmbient R r)) :
    tensorSheaf _ (commonNeighborhoodRetainedLambdaLine R V r L).val
      (commonNeighborhoodRetainedPsiLine R V r M).val ≅
    (Scheme.Modules.pullback (commonNeighborhoodRetainedInclusion R V r)).obj
      (tensorLineBundle _ (pullbackLineBundle (commonNeighborhoodToSectionAmbient R V r) L)
        (pullbackLineBundle (commonNeighborhoodToPsiAmbient R V r) M)).val :=
  tensorSheafIso _ (commonNeighborhoodRetainedLambdaPullbackIso R V r L)
    (commonNeighborhoodRetainedPsiPullbackIso R V r M) ≪≫
  (PullbackTensor.Local.pullbackLineBundleTensorIso (commonNeighborhoodRetainedInclusion R V r)
    (pullbackLineBundle (commonNeighborhoodToSectionAmbient R V r) L)
    (pullbackLineBundle (commonNeighborhoodToPsiAmbient R V r) M)).symm

/-- The product comparison preserves both original literal factor functionals. -/
theorem commonNeighborhoodRetainedProductPullbackIso_functional
    (L : LineBundle (neighborhoodSectionOpen R V r).toScheme)
    (M : LineBundle (fixedPsiAmbient R r))
    (a : L.val ⟶ SheafOfModules.unit (neighborhoodSectionOpen R V r).toScheme.ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf) :
    (commonNeighborhoodRetainedProductPullbackIso R V r L M).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.productSection
          (Scheme.Modules.Hom.pullbackToUnit a (commonNeighborhoodToSectionAmbient R V r))
          (Scheme.Modules.Hom.pullbackToUnit b (commonNeighborhoodToPsiAmbient R V r)))
        (commonNeighborhoodRetainedInclusion R V r) =
      Scheme.Modules.Hom.productSection (commonNeighborhoodRetainedLambdaFunctional R V r a)
        (commonNeighborhoodRetainedPsiFunctional R V r b) := by
  rw [Scheme.Modules.Hom.pullbackToUnit_productSection_lineBundle _
    (pullbackLineBundle (commonNeighborhoodToSectionAmbient R V r) L)
    (pullbackLineBundle (commonNeighborhoodToPsiAmbient R V r) M)]
  simp only [commonNeighborhoodRetainedProductPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorSheafIso_productSection, commonNeighborhoodRetainedLambdaPullbackIso_functional,
    commonNeighborhoodRetainedPsiPullbackIso_functional]
end AlgebraicGeometry.RelativeProjectiveLine
