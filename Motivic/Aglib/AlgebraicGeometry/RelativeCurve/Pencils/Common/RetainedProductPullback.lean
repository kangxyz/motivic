/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.RetainedSourceChange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.PencilComparison
/-! # Literal retained factor coefficients and the original compact product -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
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

variable {S X Y A B C V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a₀ : A ⟶ X)
  (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a₀) (v : V ⟶ C)

/-- Pull back the lambda line bundle through the retained product and source maps. -/
abbrev retainedLambdaLine
    (L : LineBundle (pullback (j ≫ π) π)) :=
  pullbackLineBundle (retainedToLambda π j α v)
    (pullbackLineBundle (retainedProductInclusion (j ≫ π) π v) L)

/-- Pull back the psi line bundle through the retained product and source maps. -/
abbrev retainedPsiLine (M : LineBundle (pullback (a₀ ≫ q) π)) :=
  pullbackLineBundle (retainedToPsi q π j p hq a₀ α β h v)
    (pullbackLineBundle (retainedProductInclusion (a₀ ≫ q) π v) M)

/-- Pull back the lambda functional through the retained product and source maps. -/
abbrev retainedLambdaFunctional
    {L : (pullback (j ≫ π) π).Modules}
    (f : L ⟶ SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf) :=
  Scheme.Modules.Hom.pullbackToUnit
    (Scheme.Modules.Hom.pullbackToUnit f
      (retainedProductInclusion (j ≫ π) π v))
    (retainedToLambda π j α v)

/-- Pull back the psi functional through the retained product and source maps. -/
abbrev retainedPsiFunctional {M : (pullback (a₀ ≫ q) π).Modules}
    (b : M ⟶ SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf) :=
  Scheme.Modules.Hom.pullbackToUnit
    (Scheme.Modules.Hom.pullbackToUnit b (retainedProductInclusion (a₀ ≫ q) π v))
    (retainedToPsi q π j p hq a₀ α β h v)

/-- Compare the two pullback routes for the lambda line bundle on the retained common product. -/
def retainedLambdaPullbackIso
    (L : LineBundle (pullback (j ≫ π) π)) :
    (retainedLambdaLine π j α v L).val ≅
      (Scheme.Modules.pullback (retainedProductInclusion (commonProjection π j α) π v)).obj
        ((Scheme.Modules.pullback (commonToLambda π j α)).obj L.val) :=
  commonCoefficientComparisonIso (retainedToLambda π j α v)
    (retainedProductInclusion (j ≫ π) π v)
    (retainedProductInclusion (commonProjection π j α) π v) (commonToLambda π j α)
    (retainedToLambda_inclusion π j α v) L.val

/-- Compare the two pullback routes for the psi line bundle on the retained common product. -/
def retainedPsiPullbackIso (M : LineBundle (pullback (a₀ ≫ q) π)) :
    (retainedPsiLine q π j p hq a₀ α β h v M).val ≅
      (Scheme.Modules.pullback (retainedProductInclusion (commonProjection π j α) π v)).obj
        ((Scheme.Modules.pullback (commonToPsi q π j p hq a₀ α β h)).obj M.val) :=
  commonCoefficientComparisonIso (retainedToPsi q π j p hq a₀ α β h v)
    (retainedProductInclusion (a₀ ≫ q) π v)
    (retainedProductInclusion (commonProjection π j α) π v) (commonToPsi q π j p hq a₀ α β h)
    (retainedToPsi_inclusion q π j p hq a₀ α β h v) M.val

lemma retainedLambdaPullbackIso_functional
    (L : LineBundle (pullback (j ≫ π) π))
    (f : L.val ⟶ SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf) :
    (retainedLambdaPullbackIso π j α v L).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.pullbackToUnit f (commonToLambda π j α))
        (retainedProductInclusion (commonProjection π j α) π v) =
      retainedLambdaFunctional π j α v f :=
  commonCoefficientComparison (retainedToLambda π j α v)
    (retainedProductInclusion (j ≫ π) π v)
    (retainedProductInclusion (commonProjection π j α) π v) (commonToLambda π j α)
    (retainedToLambda_inclusion π j α v) f

lemma retainedPsiPullbackIso_functional
    (M : LineBundle (pullback (a₀ ≫ q) π))
    (b : M.val ⟶ SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf) :
    (retainedPsiPullbackIso q π j p hq a₀ α β h v M).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.pullbackToUnit b (commonToPsi q π j p hq a₀ α β h))
        (retainedProductInclusion (commonProjection π j α) π v) =
      retainedPsiFunctional q π j p hq a₀ α β h v b :=
  commonCoefficientComparison (retainedToPsi q π j p hq a₀ α β h v)
    (retainedProductInclusion (a₀ ≫ q) π v)
    (retainedProductInclusion (commonProjection π j α) π v) (commonToPsi q π j p hq a₀ α β h)
    (retainedToPsi_inclusion q π j p hq a₀ α β h v) b

/-- Actual twice-retained product coefficients, not a replacement line or chosen frame. -/
def retainedProductPullbackIso
    (L : LineBundle (pullback (j ≫ π) π))
    (M : LineBundle (pullback (a₀ ≫ q) π)) :
    tensorSheaf _ (retainedLambdaLine π j α v L).val
      (retainedPsiLine q π j p hq a₀ α β h v M).val ≅
    (Scheme.Modules.pullback (retainedProductInclusion (commonProjection π j α) π v)).obj
      (tensorLineBundle _ (pullbackLineBundle (commonToLambda π j α) L)
        (pullbackLineBundle (commonToPsi q π j p hq a₀ α β h) M)).val :=
  tensorSheafIso _ (retainedLambdaPullbackIso π j α v L)
    (retainedPsiPullbackIso q π j p hq a₀ α β h v M) ≪≫
  (PullbackTensor.Local.pullbackLineBundleTensorIso
    (retainedProductInclusion (commonProjection π j α) π v)
    (pullbackLineBundle (commonToLambda π j α) L)
    (pullbackLineBundle (commonToPsi q π j p hq a₀ α β h) M)).symm

/-- The product comparison preserves both original literal factor functionals. -/
theorem retainedProductPullbackIso_functional
    (L : LineBundle (pullback (j ≫ π) π))
    (M : LineBundle (pullback (a₀ ≫ q) π))
    (f : L.val ⟶ SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf)
    (b : M.val ⟶ SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf) :
    (retainedProductPullbackIso q π j p hq a₀ α β h v L M).hom ≫
      Scheme.Modules.Hom.pullbackToUnit
        (Scheme.Modules.Hom.productSection
          (Scheme.Modules.Hom.pullbackToUnit f (commonToLambda π j α))
          (Scheme.Modules.Hom.pullbackToUnit b (commonToPsi q π j p hq a₀ α β h)))
        (retainedProductInclusion (commonProjection π j α) π v) =
      Scheme.Modules.Hom.productSection (retainedLambdaFunctional π j α v f)
        (retainedPsiFunctional q π j p hq a₀ α β h v b) := by
  rw [Scheme.Modules.Hom.pullbackToUnit_productSection_lineBundle _
    (pullbackLineBundle (commonToLambda π j α) L)
    (pullbackLineBundle (commonToPsi q π j p hq a₀ α β h) M)]
  simp only [retainedProductPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorSheafIso_productSection, retainedLambdaPullbackIso_functional,
    retainedPsiPullbackIso_functional]
end AlgebraicGeometry.Scheme.RelativeCurvePencil
