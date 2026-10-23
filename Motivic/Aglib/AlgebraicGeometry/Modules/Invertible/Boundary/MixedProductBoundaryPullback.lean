/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.MixedBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.GlobalBoundaryPencil
/-! # Literal compact product pencils restricted through two original source maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem pullbackToUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : M ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    Hom.pullbackToUnit (Hom.pullbackToUnit a g) f =
      (Modules.pullbackComp f g).hom.app M ≫ Hom.pullbackToUnit a (f ≫ g) :=
  GlobalBoundaryPencil.pullback_map_comp f g a

/-- The genuine product functional on the common compactification. -/
def mixedProductFunctional {X Y C : Scheme.{u}} (f : C ⟶ X) (g : C ⟶ Y)
    (L : LineBundle X) (M : LineBundle Y)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b : SheafOfModules.unit Y.ringCatSheaf ⟶ M.val) :=
  Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X L a) f)
    (Hom.pullbackToUnit (sectionDualFunctional Y M b) g)

/-- The actual boundary tensor equation equates restrictions of the original compact
product functionals. No replacement of the global comparison by a boundary-only one occurs. -/
theorem mixedProductFunctional_boundary {X Y C W : Scheme.{u}}
    (f : C ⟶ X) (g : C ⟶ Y) (j : W ⟶ C) (L : LineBundle X) (M : LineBundle Y)
    (a a' : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b b' : SheafOfModules.unit Y.ringCatSheaf ⟶ M.val)
    (h : tensorSectionMap W (pullbackSectionMap (j ≫ f) a)
        (pullbackSectionMap (j ≫ g) b) =
      tensorSectionMap W (pullbackSectionMap (j ≫ f) a')
        (pullbackSectionMap (j ≫ g) b')) :
    Hom.pullbackToUnit (mixedProductFunctional f g L M a b) j =
      Hom.pullbackToUnit (mixedProductFunctional f g L M a' b') j := by
  change Hom.pullbackToUnit (Hom.productSection _ _) j =
    Hom.pullbackToUnit (Hom.productSection _ _) j
  rw [Hom.pullbackToUnit_productSection_lineBundle j
    (pullbackLineBundle f (dualLineBundle X L)) (pullbackLineBundle g (dualLineBundle Y M)),
    Hom.pullbackToUnit_productSection_lineBundle j
    (pullbackLineBundle f (dualLineBundle X L)) (pullbackLineBundle g (dualLineBundle Y M))]
  rw [pullbackToUnit_comp, pullbackToUnit_comp, pullbackToUnit_comp, pullbackToUnit_comp]
  rw [← Hom.productSection_naturality, ← Hom.productSection_naturality]
  rw [tensorSection_eq_product_mixedPulledSectionDualFunctional (j ≫ f) (j ≫ g)
    L M a a' b b' h]

/-- Two genuine unit-valued factors have an invertible original product functional. -/
theorem productSection_isIso {W : Scheme.{u}} {L M : W.Modules}
    (a : L ⟶ SheafOfModules.unit W.ringCatSheaf)
    (b : M ⟶ SheafOfModules.unit W.ringCatSheaf) [IsIso a] [IsIso b] :
    IsIso (Hom.productSection a b) := by
  change IsIso (tensorSheafMap W a (𝟙 M) ≫ (tensorSheafLeftUnit W M).hom ≫ b)
  have : IsIso (tensorSheafMap W a (𝟙 M)) := by
    change IsIso (tensorSheafIso W (asIso a) (Iso.refl M)).hom
    infer_instance
  infer_instance

/-- The actual compact product functional is a unit on a boundary where both original
normalized section values are units. -/
theorem mixedProductFunctional_boundary_isIso {X Y C W : Scheme.{u}}
    (f : C ⟶ X) (g : C ⟶ Y) (j : W ⟶ C) (L : LineBundle X) (M : LineBundle Y)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b : SheafOfModules.unit Y.ringCatSheaf ⟶ M.val)
    [IsIso (pullbackSectionMap (j ≫ f) a)] [IsIso (pullbackSectionMap (j ≫ g) b)] :
    IsIso (Hom.pullbackToUnit (mixedProductFunctional f g L M a b) j) := by
  have := sectionDualFunctional_pullback_isIso (j ≫ f) L a
  have := sectionDualFunctional_pullback_isIso (j ≫ g) M b
  have hA : IsIso (Hom.pullbackToUnit (Hom.pullbackToUnit (sectionDualFunctional X L a) f) j) := by
    rw [pullbackToUnit_comp]
    infer_instance
  have hB : IsIso (Hom.pullbackToUnit (Hom.pullbackToUnit (sectionDualFunctional Y M b) g) j) := by
    rw [pullbackToUnit_comp]
    infer_instance
  change IsIso (Hom.pullbackToUnit (Hom.productSection _ _) j)
  rw [Hom.pullbackToUnit_productSection_lineBundle j
    (pullbackLineBundle f (dualLineBundle X L)) (pullbackLineBundle g (dualLineBundle Y M))]
  have := productSection_isIso
    (Hom.pullbackToUnit (Hom.pullbackToUnit (sectionDualFunctional X L a) f) j)
    (Hom.pullbackToUnit (Hom.pullbackToUnit (sectionDualFunctional Y M b) g) j)
  infer_instance
end AlgebraicGeometry.Scheme.Modules.Invertible
