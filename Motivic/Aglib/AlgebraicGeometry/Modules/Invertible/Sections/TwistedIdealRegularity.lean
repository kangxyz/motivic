/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.RegularProductSections
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.Product

/-! # Regularity of the original graph-twisted section

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Sections.TwistedIdealRegularity`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.GraphCancelledNormDifference`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.OriginalPairNormDifference`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Regularity of the original twisted section follows from the ideal inclusion and
its original pole functional. It does not assert a unit on the marked incidence. -/
theorem twistedIdealSection_mono (X : Scheme.{u}) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ]
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    [Mono (sectionDualFunctional X T s)] :
    Mono (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
      (twistedIdealSection X I T φ s)) := by
  have : Mono (Hom.productSection φ (sectionDualFunctional X T s)) :=
    Hom.productSection_mono I (dualLineBundle X T) φ (sectionDualFunctional X T s)
  have : Mono ((dualTwistedIdealIso X I T).hom ≫
      sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
        (twistedIdealSection X I T φ s)) := by
    rw [dualTwistedIdealIso_section]
    infer_instance
  have hmono : Mono ((dualTwistedIdealIso X I T).inv ≫
      ((dualTwistedIdealIso X I T).hom ≫
        sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ s))) := inferInstance
  simpa only [Iso.inv_hom_id_assoc] using hmono

end AlgebraicGeometry.Scheme.Modules.Invertible
