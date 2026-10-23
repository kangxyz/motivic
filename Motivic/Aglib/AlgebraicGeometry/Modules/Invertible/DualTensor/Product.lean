/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTensor.PairingLaw
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Naturality
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.Product.Associator
/-! # Literal divisor product compatibility of the actual dual twist -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The original global identification retains the literal divisor/section product. -/
theorem dualTwistedIdealIso_section (X : Scheme.{u}) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val) :
    (dualTwistedIdealIso X I T).hom ≫
      sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
        (twistedIdealSection X I T φ s) =
      Hom.productSection φ (sectionDualFunctional X T s) :=
  dualTwistedIdeal_section_of_pairing X I T (dualTwistedIdealIso X I T).hom
    (dualTwistedIdealIso_pairing X I T) φ s

/-- The exact three-factor line comparison retains the original product section. -/
theorem dualTwistedIdealProductIso_section (X : Scheme.{u}) (I T S : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (b : (dualLineBundle X S).val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (dualTwistedIdealProductIso X I T S).hom ≫
      Hom.productSection
        (sectionDualFunctional X (tensorLineBundle X T (dualLineBundle X I))
          (twistedIdealSection X I T φ s)) b =
      Hom.productSection φ (Hom.productSection (sectionDualFunctional X T s) b) := by
  simp only [dualTwistedIdealProductIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (tensorLineBundleAssociator X I (dualLineBundle X T) (dualLineBundle X S)).inv ≫
    tensorSheafMap X (dualTwistedIdealIso X I T).hom (𝟙 (dualLineBundle X S).val) ≫ _ = _
  rw [Hom.productSection_naturality, Category.id_comp, dualTwistedIdealIso_section]
  have h := Hom.productSection_associator I (dualLineBundle X T) (dualLineBundle X S)
    φ (sectionDualFunctional X T s) b
  rw [← h, Iso.inv_hom_id_assoc]
end AlgebraicGeometry.Scheme.Modules.Invertible
