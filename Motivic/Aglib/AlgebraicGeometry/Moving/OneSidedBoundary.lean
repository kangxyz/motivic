/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Product
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TensorSectionPullback
/-! # One-sided moving: only the missing boundary constrains the homotopy

The numerator and denominator will avoid the larger bad boundary. The pencil itself
only avoids infinity, since its diagonal endpoint may meet the bad closed subset.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Moving
variable {C D : Scheme.{u}} (f : D ⟶ C) (I T : LineBundle C)
  (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
  (b : SheafOfModules.unit C.ringCatSheaf ⟶ T.val)
  (a : SheafOfModules.unit C.ringCatSheaf ⟶
    (tensorLineBundle C T (dualLineBundle C I)).val)
  (E : (Modules.pullback f).obj (dualLineBundle C I).val ≅
    SheafOfModules.unit D.ringCatSheaf)

/-- On infinity the prescribed frame is the original canonical diagonal section,
so the actual Serre numerator equals the actual diagonal times denominator there. -/
theorem oneSided_boundary_section
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle C I).val =
      tensorUnitSection (pullbackSectionMap f b) E.inv)
    (hδ : pullbackSectionMap f (canonicalDualHom C I.val φ) ≫ E.hom = 𝟙 _) :
    pullbackSectionMap f a = pullbackSectionMap f (twistedIdealSection C I T φ b) := by
  have he : pullbackSectionMap f (canonicalDualHom C I.val φ) = E.inv := by
    apply (cancel_mono E.hom).mp
    rw [hδ, Iso.inv_hom_id]
  have : IsIso (pullbackTensorMap f T.val (dualLineBundle C I).val) :=
    PullbackTensor.Local.pullbackTensorMap_isIso f T.val (dualLineBundle C I).val T.property
  apply (cancel_mono (pullbackTensorMap f T.val (dualLineBundle C I).val)).mp
  rw [ha]
  have ht := pullbackSectionMap_tensorUnitSection f b (canonicalDualHom C I.val φ)
  change pullbackSectionMap f (twistedIdealSection C I T φ b) ≫
    pullbackTensorMap f T.val (dualLineBundle C I).val = _ at ht
  rw [ht, he]

/-- The actual global line comparison, not only its Picard class, gives equality
of the two polynomial-pencil functionals on infinity. -/
theorem oneSided_boundary_functional
    (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle C I).val =
      tensorUnitSection (pullbackSectionMap f b) E.inv)
    (hδ : pullbackSectionMap f (canonicalDualHom C I.val φ) ≫ E.hom = 𝟙 _) :
    Hom.pullbackToUnit
      ((dualTwistedIdealIso C I T).hom ≫
        sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I)) a) f =
      Hom.pullbackToUnit (Hom.productSection φ (sectionDualFunctional C T b)) f := by
  have hs := oneSided_boundary_section f I T φ b a E ha hδ
  have hf : Hom.pullbackToUnit
      (sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I)) a) f =
      Hom.pullbackToUnit
        (sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I))
          (twistedIdealSection C I T φ b)) f := by
    rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
    simp only [pulledSectionDualFunctional, hs]
  change (Modules.pullback f).map ((dualTwistedIdealIso C I T).hom ≫ _) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  change (Modules.pullback f).map (dualTwistedIdealIso C I T).hom ≫
    Hom.pullbackToUnit (sectionDualFunctional C
      (tensorLineBundle C T (dualLineBundle C I)) a) f = _
  rw [hf]
  change (Modules.pullback f).map (dualTwistedIdealIso C I T).hom ≫
    (Modules.pullback f).map (sectionDualFunctional C
      (tensorLineBundle C T (dualLineBundle C I)) (twistedIdealSection C I T φ b)) ≫
      (pullbackUnitIso f).hom = _
  rw [← Functor.map_comp_assoc, dualTwistedIdealIso_section]
  rfl

end AlgebraicGeometry.Scheme.Moving
