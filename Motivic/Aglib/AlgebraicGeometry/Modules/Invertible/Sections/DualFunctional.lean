/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.RightUnit
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryCanonicalCoordinate

/-! # The actual dual functional of a section and arbitrary pullback -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A supplied actual section defines its original dual evaluation functional. -/
def sectionDualFunctional (X : Scheme.{u}) (L : LineBundle X)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) :
    (dualLineBundle X L).val ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (tensorSheafRightUnit X (dualLineBundle X L).val).inv ≫
    tensorSheafMap X (𝟙 _) s ≫ (dualEvaluationIso X L).hom

/-- Pullback of a section through the original structure-module unit comparison. -/
def pullbackSectionMap {X W : Scheme.{u}} (f : W ⟶ X)
    {M : X.Modules} (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    SheafOfModules.unit W.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s

/-- The original pulled evaluation functional, with the actual tensor comparison. -/
def pulledSectionDualFunctional {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) :
    (Scheme.Modules.pullback f).obj (dualLineBundle X L).val ⟶
      SheafOfModules.unit W.ringCatSheaf :=
  (tensorSheafRightUnit W ((Scheme.Modules.pullback f).obj (dualLineBundle X L).val)).inv ≫
    tensorSheafMap W (𝟙 _) (pullbackSectionMap f s) ≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).inv ≫
    (Scheme.Modules.pullback f).map (dualEvaluationIso X L).hom ≫ (pullbackUnitIso f).hom

/-- Actual dualization commutes with arbitrary pullback, without a flatness premise. -/
theorem sectionDualFunctional_pullback {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) :
    Hom.pullbackToUnit (sectionDualFunctional X L s) f = pulledSectionDualFunctional f L s := by
  let D := (dualLineBundle X L).val
  apply (cancel_epi ((Scheme.Modules.pullback f).map (tensorSheafRightUnit X D).hom)).mp
  unfold Hom.pullbackToUnit sectionDualFunctional pulledSectionDualFunctional pullbackSectionMap
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← pullbackTensorMap_rightUnit f D]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc]
  rw [tensorSheafMap_comp_assoc]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  have hn := pullbackTensorMap_naturality f (𝟙 D) s
  rw [CategoryTheory.Functor.map_id] at hn
  rw [← Category.assoc (pullbackTensorMap f D _), ← hn]
  simp only [Category.assoc]
  change _ = (Scheme.Modules.pullback f).map (tensorSheafMap X (𝟙 D) s) ≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle X L) L).hom ≫ _
  rw [Iso.hom_inv_id_assoc]

/-- A section invertible on the boundary gives an invertible actual dual functional there. -/
theorem sectionDualFunctional_pullback_isIso {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap f s)] :
    IsIso (Hom.pullbackToUnit (sectionDualFunctional X L s) f) := by
  rw [sectionDualFunctional_pullback]
  change IsIso (Scheme.Hom.dualBoundaryTrivialization f L (asIso (pullbackSectionMap f s))).hom
  infer_instance

/-- The actual zero scheme of the dual section misses any boundary where the section is a unit. -/
theorem sectionDualFunctional_boundary_isEmpty {X W : Scheme.{u}} (f : W ⟶ X)
    (L : LineBundle X) (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap f s)] :
    IsEmpty (Limits.pullback (C := Scheme.{u}) f
      (Hom.zeroInclusion (sectionDualFunctional X L s))) := by
  let := lineBundle_isLocallyFree X (dualLineBundle X L)
  have := sectionDualFunctional_pullback_isIso f L s
  exact Hom.isEmpty_pullback_zeroInclusion (sectionDualFunctional X L s) f

end AlgebraicGeometry.Scheme.Modules.Invertible
