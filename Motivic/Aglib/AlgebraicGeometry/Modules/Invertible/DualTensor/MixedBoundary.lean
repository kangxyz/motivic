/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Boundary
/-! # Original line comparison with independent lambda and psi source maps -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Two independent pullbacks retain the two original evaluation maps. -/
theorem tensorSection_eq_product_mixedPulledSectionDualFunctional
    {X Y W : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)
    (L : LineBundle X) (M : LineBundle Y)
    (a a' : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    (b b' : SheafOfModules.unit Y.ringCatSheaf ⟶ M.val)
    (h : tensorSectionMap W (pullbackSectionMap f a) (pullbackSectionMap g b) =
      tensorSectionMap W (pullbackSectionMap f a') (pullbackSectionMap g b')) :
    Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X L a) f)
      (Hom.pullbackToUnit (sectionDualFunctional Y M b) g) =
    Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X L a') f)
      (Hom.pullbackToUnit (sectionDualFunctional Y M b') g) := by
  simp only [sectionDualFunctional_pullback]
  exact tensorSection_eq_product_pairedSectionFunctional W
    (pullbackLineBundle f (dualLineBundle X L)) (pullbackLineBundle g (dualLineBundle Y M))
    (pullbackLineBundle f L) (pullbackLineBundle g M)
    ((PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
      (Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom)
    ((PullbackTensor.Local.pullbackLineBundleTensorIso g (dualLineBundle Y M) M).inv ≫
      (Modules.pullback g).map (dualEvaluationIso Y M).hom ≫ (pullbackUnitIso g).hom)
    (pullbackSectionMap f a) (pullbackSectionMap g b)
    (pullbackSectionMap f a') (pullbackSectionMap g b') h

/-- The actual two-factor global comparison under the lambda source pullback. -/
def pulledDualTwistedIdealIso {X W : Scheme.{u}} (f : W ⟶ X) (I T : LineBundle X) :
    tensorSheaf W ((Modules.pullback f).obj I.val)
      ((Modules.pullback f).obj (dualLineBundle X T).val) ≅
      (Modules.pullback f).obj (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val :=
  (PullbackTensor.Local.pullbackLineBundleTensorIso f I (dualLineBundle X T)).symm ≪≫
    (Modules.pullback f).mapIso (dualTwistedIdealIso X I T)

theorem pulledDualTwistedIdealIso_section {X W : Scheme.{u}} (f : W ⟶ X)
    (I T : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) :
    (pulledDualTwistedIdealIso f I T).hom ≫
      Hom.pullbackToUnit (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
        (twistedIdealSection X I T φ b)) f =
      Hom.productSection (Hom.pullbackToUnit φ f)
        (Hom.pullbackToUnit (sectionDualFunctional X T b) f) := by
  simp only [pulledDualTwistedIdealIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  change (PullbackTensor.Local.pullbackLineBundleTensorIso f I (dualLineBundle X T)).inv ≫
    (Modules.pullback f).map (dualTwistedIdealIso X I T).hom ≫
    (Modules.pullback f).map _ ≫ (pullbackUnitIso f).hom = _
  rw [← Functor.map_comp_assoc, dualTwistedIdealIso_section]
  change (PullbackTensor.Local.pullbackLineBundleTensorIso f I (dualLineBundle X T)).inv ≫
    Hom.pullbackToUnit (Hom.productSection φ (sectionDualFunctional X T b)) f = _
  rw [Hom.pullbackToUnit_productSection_lineBundle, Iso.inv_hom_id_assoc]

/-- The original lambda comparison tensored with the independently pulled psi dual. -/
def mixedPulledDualTwistedIdealProductIso {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y) :
    tensorSheaf W ((Modules.pullback f).obj I.val)
      (tensorSheaf W ((Modules.pullback f).obj (dualLineBundle X T).val)
        ((Modules.pullback g).obj (dualLineBundle Y S).val)) ≅
    tensorSheaf W
      ((Modules.pullback f).obj
        (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val)
      ((Modules.pullback g).obj (dualLineBundle Y S).val) :=
  (tensorLineBundleAssociator W (pullbackLineBundle f I)
    (pullbackLineBundle f (dualLineBundle X T))
    (pullbackLineBundle g (dualLineBundle Y S))).symm ≪≫
      tensorSheafIso W (pulledDualTwistedIdealIso f I T) (Iso.refl _)

/-- The mixed-source line comparison retains the original three-factor product. -/
theorem mixedPulledDualTwistedIdealProductIso_section {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d : SheafOfModules.unit Y.ringCatSheaf ⟶ S.val) :
    (mixedPulledDualTwistedIdealProductIso f g I T S).hom ≫
      Hom.productSection
        (Hom.pullbackToUnit (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ b)) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S d) g) =
    Hom.productSection (Hom.pullbackToUnit φ f)
      (Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X T b) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S d) g)) := by
  simp only [mixedPulledDualTwistedIdealProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (tensorLineBundleAssociator W (pullbackLineBundle f I)
    (pullbackLineBundle f (dualLineBundle X T))
    (pullbackLineBundle g (dualLineBundle Y S))).inv ≫
      tensorSheafMap W (pulledDualTwistedIdealIso f I T).hom (𝟙 _) ≫ _ = _
  rw [Hom.productSection_naturality, Category.id_comp, pulledDualTwistedIdealIso_section]
  rw [← Hom.productSection_associator (pullbackLineBundle f I)
    (pullbackLineBundle f (dualLineBundle X T)) (pullbackLineBundle g (dualLineBundle Y S))]
  rw [Iso.inv_hom_id_assoc]

/-- The actual mixed-source boundary tensor equation gives the original functional equation;
no common source scheme for the two twists or dual pullback identification is assumed. -/
theorem mixedPulledDualTwistedIdealProductIso_boundary {X Y W : Scheme.{u}}
    (f : W ⟶ X) (g : W ⟶ Y) (I T : LineBundle X) (S : LineBundle Y)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (d n : SheafOfModules.unit Y.ringCatSheaf ⟶ S.val)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (h : tensorSectionMap W (pullbackSectionMap f a) (pullbackSectionMap g n) =
      tensorSectionMap W (pullbackSectionMap f (twistedIdealSection X I T φ b))
        (pullbackSectionMap g d)) :
    (mixedPulledDualTwistedIdealProductIso f g I T S).hom ≫
      Hom.productSection
        (Hom.pullbackToUnit
          (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I)) a) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S n) g) =
    Hom.productSection (Hom.pullbackToUnit φ f)
      (Hom.productSection (Hom.pullbackToUnit (sectionDualFunctional X T b) f)
        (Hom.pullbackToUnit (sectionDualFunctional Y S d) g)) := by
  rw [tensorSection_eq_product_mixedPulledSectionDualFunctional f g
    (tensorLineBundle X T (dualLineBundle X I)) S a (twistedIdealSection X I T φ b) n d h]
  exact mixedPulledDualTwistedIdealProductIso_section f g I T S φ b d
end AlgebraicGeometry.Scheme.Modules.Invertible
