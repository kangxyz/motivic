/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.DualFunctional
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator

/-! # Actual dual of a twist tensored with a divisor dual -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u}) (I T : LineBundle X)

/-- The two literal ordered tensor products are paired by the original evaluations. -/
def twistedIdealPairingIso :
    tensorSheaf X (tensorLineBundle X I (dualLineBundle X T)).val
      (tensorLineBundle X T (dualLineBundle X I)).val ≅
      SheafOfModules.unit X.ringCatSheaf :=
  tensorLineBundleAssociator X I (dualLineBundle X T)
      (tensorLineBundle X T (dualLineBundle X I)) ≪≫
    tensorSheafIso X (Iso.refl I.val)
      (tensorLineBundleAssociator X (dualLineBundle X T) T (dualLineBundle X I)).symm ≪≫
    tensorSheafIso X (Iso.refl I.val)
      (tensorSheafIso X (dualEvaluationIso X T) (Iso.refl (dualLineBundle X I).val)) ≪≫
    tensorSheafIso X (Iso.refl I.val) (tensorSheafLeftUnit X (dualLineBundle X I).val) ≪≫
    tensorSheafBraiding X I.val (dualLineBundle X I).val ≪≫ dualEvaluationIso X I

/-- Canonical actual identification of the twisted ideal with the dual of its inverse twist. -/
def dualTwistedIdealIso :
    (tensorLineBundle X I (dualLineBundle X T)).val ≅
      (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val := by
  let M := tensorLineBundle X I (dualLineBundle X T)
  let N := tensorLineBundle X T (dualLineBundle X I)
  let eN : tensorSheaf X N.val (dualLineBundle X N).val ≅
      SheafOfModules.unit X.ringCatSheaf :=
    tensorSheafBraiding X N.val (dualLineBundle X N).val ≪≫ dualEvaluationIso X N
  exact (tensorSheafRightUnit X M.val).symm ≪≫
    tensorSheafIso X (Iso.refl M.val) eN.symm ≪≫
    (tensorLineBundleAssociator X M N (dualLineBundle X N)).symm ≪≫
    tensorSheafIso X (twistedIdealPairingIso X I T)
      (Iso.refl (dualLineBundle X N).val) ≪≫
    tensorSheafLeftUnit X (dualLineBundle X N).val

/-- The exact line-bundle domain comparison used by the product-section data. -/
def dualTwistedIdealProductIso (S : LineBundle X) :
    tensorSheaf X I.val
      (tensorSheaf X (dualLineBundle X T).val (dualLineBundle X S).val) ≅
    tensorSheaf X (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val
      (dualLineBundle X S).val :=
  (tensorLineBundleAssociator X I (dualLineBundle X T) (dualLineBundle X S)).symm ≪≫
    tensorSheafIso X (dualTwistedIdealIso X I T) (Iso.refl (dualLineBundle X S).val)

end AlgebraicGeometry.Scheme.Modules.Invertible
