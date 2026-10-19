/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramed
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.PerfectPairingDual

/-!
# Transport of actual sections preserving boundary frames

A frame-preserving isomorphism identifies the literal pulled sections, not just
ordinary Picard classes. Its dual comparison preserves evaluation and hence the
original zero functional. Whole-zero and correspondence comparisons can then
use the existing source-isomorphism interfaces.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {C D : Scheme.{u}} {L M : LineBundle C}

/-- Dual precomposition along the original line isomorphism, constructed from the
native evaluation pairing rather than a replacement dual sheaf. -/
def dualPrecompIso (E : L.val ≅ M.val) :
    (dualLineBundle C M).val ≅ (dualLineBundle C L).val :=
  perfectPairingDualIso C (dualLineBundle C M) L
    (tensorSheafIso C (CategoryTheory.Iso.refl _) E ≪≫ dualEvaluationIso C M)

/-- The actual dual comparison intertwines the original evaluation maps. -/
theorem dualPrecompIso_pairing (E : L.val ≅ M.val) :
    tensorSheafMap C (dualPrecompIso E).hom (𝟙 L.val) ≫ (dualEvaluationIso C L).hom =
      tensorSheafMap C (𝟙 (dualLineBundle C M).val) E.hom ≫
        (dualEvaluationIso C M).hom :=
  perfectPairingDualIso_pairing C (dualLineBundle C M) L _

/-- Transporting the original section precomposes its zero functional by the actual
native dual isomorphism. -/
theorem sectionDualFunctional_postcompIso (E : L.val ≅ M.val)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val) :
    sectionDualFunctional C M (s ≫ E.hom) =
      (dualPrecompIso E).hom ≫ sectionDualFunctional C L s := by
  rw [comp_sectionDualFunctional]
  have ht : tensorSheafMap C (dualPrecompIso E).hom s =
      tensorSheafMap C (𝟙 (dualLineBundle C M).val) s ≫
        tensorSheafMap C (dualPrecompIso E).hom (𝟙 L.val) := by
    rw [tensorSheafMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  rw [ht]
  simp only [Category.assoc]
  rw [dualPrecompIso_pairing]
  unfold sectionDualFunctional
  rw [tensorSheafMap_comp_assoc]
  simp only [Category.id_comp]

/-- The original pullback of the zero functional is invertible whenever the section
is invertible on the boundary; the canonical unit comparison is retained. -/
theorem sectionDualFunctional_pullback_map_isIso (i : D ⟶ C) (L : LineBundle C)
    (s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap i s)] :
    IsIso ((Modules.pullback i).map (sectionDualFunctional C L s)) := by
  have := sectionDualFunctional_pullback_isIso i L s
  have h : (Modules.pullback i).map (sectionDualFunctional C L s) =
      Hom.pullbackToUnit (sectionDualFunctional C L s) i ≫ (pullbackUnitIso i).inv := by
    simp only [Hom.pullbackToUnit, Category.assoc, CategoryTheory.Iso.hom_inv_id,
      Category.comp_id]
  rw [h]
  infer_instance

namespace BoundaryFramedLineBundle

variable {i : D ⟶ C}
    {s : SheafOfModules.unit C.ringCatSheaf ⟶ L.val}
    {t : SheafOfModules.unit C.ringCatSheaf ⟶ M.val}
    [IsIso (pullbackSectionMap i s)] [IsIso (pullbackSectionMap i t)]

/-- Preserving the inverse boundary frames preserves the original pulled sections. -/
theorem Iso.pullbackSectionMap_eq (e : Iso (ofSection i L s) (ofSection i M t)) :
    pullbackSectionMap i (s ≫ e.iso.hom) = pullbackSectionMap i t := by
  apply (cancel_mono (ofSection i M t).frame.hom).mp
  change pullbackSectionMap i (s ≫ e.iso.hom) ≫ (ofSection i M t).frame.hom =
    (ofSection i M t).frame.inv ≫ (ofSection i M t).frame.hom
  rw [CategoryTheory.Iso.inv_hom_id]
  change (pullbackUnitIso i).inv ≫ (Modules.pullback i).map (s ≫ e.iso.hom) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [e.frame_hom]
  change (ofSection i L s).frame.inv ≫ (ofSection i L s).frame.hom = _
  exact CategoryTheory.Iso.inv_hom_id _

/-- The transported numerator and the original second section have exactly equal
whole-boundary zero functionals. -/
theorem Iso.pullbackToUnit_sectionDualFunctional_eq
    (e : Iso (ofSection i L s) (ofSection i M t)) :
    Hom.pullbackToUnit (sectionDualFunctional C M (s ≫ e.iso.hom)) i =
      Hom.pullbackToUnit (sectionDualFunctional C M t) i := by
  rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
  unfold pulledSectionDualFunctional
  rw [e.pullbackSectionMap_eq]

end BoundaryFramedLineBundle

end AlgebraicGeometry.Scheme.Modules.Invertible
