/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.RetainedProductPullback
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.RetainedGraphIdeal
/-! # The actual retained graph-domain line and its canonical start functional -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
variable {S X Y A B C V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a₀ : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a₀) (v : V ⟶ C)
/-- Native pullback composition through the lambda retained curve. -/
def retainedLambdaCompositeIso :
    Modules.pullback (retainedProductInclusion (j ≫ π) π v) ⋙
      Modules.pullback (retainedToLambda π j α v) ≅
    Modules.pullback (retainedProductInclusion (commonProjection π j α) π v ≫
      commonToLambda π j α) :=
  Modules.pullbackComp _ _ ≪≫
    Modules.pullbackCongr (retainedToLambda_inclusion π j α v)

/-- Native pullback composition through the unchanged fixed-U retained curve. -/
def retainedPsiCompositeIso :
    Modules.pullback (retainedProductInclusion (a₀ ≫ q) π v) ⋙
      Modules.pullback (retainedToPsi q π j p hq a₀ α β h v) ≅
    Modules.pullback (retainedProductInclusion (commonProjection π j α) π v ≫
      commonToPsi q π j p hq a₀ α β h) :=
  Modules.pullbackComp _ _ ≪≫
    Modules.pullbackCongr (retainedToPsi_inclusion q π j p hq a₀ α β h v)

theorem retainedLambdaFunctional_eq {L : (pullback (j ≫ π) π).Modules}
    (a : L ⟶ SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf) :
    retainedLambdaFunctional π j α v a =
      (retainedLambdaCompositeIso π j α v).hom.app L ≫
        Hom.pullbackToUnit a
          (retainedProductInclusion (commonProjection π j α) π v ≫
            commonToLambda π j α) :=
  pullbackToUnit_comp_congr _ _ _ _ _

theorem retainedPsiFunctional_eq {L : (pullback (a₀ ≫ q) π).Modules}
    (a : L ⟶ SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf) :
    retainedPsiFunctional q π j p hq a₀ α β h v a =
      (retainedPsiCompositeIso q π j p hq a₀ α β h v).hom.app L ≫
        Hom.pullbackToUnit a
          (retainedProductInclusion (commonProjection π j α) π v ≫
            commonToPsi q π j p hq a₀ α β h) :=
  pullbackToUnit_comp_congr _ _ _ _ _

variable [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  [IsOpenImmersion v] (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
  [Flat α] (T : LineBundle (pullback (j ≫ π) π))
  (N : LineBundle (pullback (a₀ ≫ q) π))

/-- Local rank one is inherited from the original lambda ideal, not assumed. -/
theorem commonRetainedGraph_locallyRankOne :
    IsLocallyRankOne _ (Hom.idealModule (relativeRetainedGraph π j α v φ hφ)) :=
  isLocallyRankOne_of_iso _ (relativeRetainedGraphIdealIso π j α v φ hφ)
    (pullbackLineBundle
      (retainedProductInclusion (commonProjection π j α) π v ≫
        commonToLambda π j α) (Hom.relativeCompactificationGraphLine π j)).property

/-- The original mixed dual comparison, conjugated only by native pullback composition
and the canonical ideal of the actual retained graph. -/
def retainedPencilLineIso :
    tensorSheaf _ (Hom.idealModule (relativeRetainedGraph π j α v φ hφ))
      (tensorSheaf _
        (retainedLambdaLine π j α v (dualLineBundle _ T)).val
        (retainedPsiLine q π j p hq a₀ α β h v (dualLineBundle _ N)).val) ≅
    tensorSheaf _
      (retainedLambdaLine π j α v
        (dualLineBundle _ (tensorLineBundle _ T (dualLineBundle _
          (Hom.relativeCompactificationGraphLine π j))))).val
      (retainedPsiLine q π j p hq a₀ α β h v (dualLineBundle _ N)).val :=
  tensorSheafIso _ (relativeRetainedGraphIdealIso π j α v φ hφ).symm
    (tensorSheafIso _
      ((retainedLambdaCompositeIso π j α v).app (dualLineBundle _ T).val)
      ((retainedPsiCompositeIso q π j p hq a₀ α β h v).app (dualLineBundle _ N).val)) ≪≫
  mixedPulledDualTwistedIdealProductIso
    (retainedProductInclusion (commonProjection π j α) π v ≫
      commonToLambda π j α)
    (retainedProductInclusion (commonProjection π j α) π v ≫
      commonToPsi q π j p hq a₀ α β h) (Hom.relativeCompactificationGraphLine π j) T N ≪≫
  tensorSheafIso _
    ((retainedLambdaCompositeIso π j α v).app
      (dualLineBundle _ (tensorLineBundle _ T (dualLineBundle _
        (Hom.relativeCompactificationGraphLine π j)))).val).symm
    ((retainedPsiCompositeIso q π j p hq a₀ α β h v).app (dualLineBundle _ N).val).symm

/-- Endpoint zero is the literal retained graph times the original two pole maps. -/
theorem retainedPencilLineIso_start
    (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf ⟶ N.val) :
    (retainedPencilLineIso q π j p hq a₀ α β h v φ hφ T N).hom ≫
      Hom.productSection
        (retainedLambdaFunctional π j α v
          (sectionDualFunctional _ (tensorLineBundle _ T (dualLineBundle _
            (Hom.relativeCompactificationGraphLine π j)))
            (twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) T
              (Hom.idealInclusion
                (Hom.compactificationGraph π j)) b)))
        (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N d)) =
    Hom.productSection (Hom.idealInclusion (relativeRetainedGraph π j α v φ hφ))
      (Hom.productSection
        (retainedLambdaFunctional π j α v (sectionDualFunctional _ T b))
        (retainedPsiFunctional q π j p hq a₀ α β h v (sectionDualFunctional _ N d))) := by
  simp only [retainedLambdaFunctional_eq π j α v,
    retainedPsiFunctional_eq q π j p hq a₀ α β h v]
  simp only [retainedPencilLineIso, Iso.trans_hom, Category.assoc]
  rw [tensorSheafIso_productSection]
  simp only [Iso.symm_hom, Iso.app_inv,
    Iso.inv_hom_id_app_assoc]
  rw [mixedPulledDualTwistedIdealProductIso_section]
  rw [tensorSheafIso_productSection, tensorSheafIso_productSection]
  congr 1
  rw [← relativeRetainedGraphIdealIso_inclusion π j α v φ hφ]
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
