/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.GraphInfinityEquality
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.TensorSections

/-! # The graph ratio on its actual unit boundary

The original prescribed pair gives the graph-twisted denominator as the original
coordinate times the numerator. Inverting it is permitted only where that
coordinate is a unit, as happens after actual disjoint-source restriction.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.PrescribedGraphRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.GraphRatioBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X W : Scheme.{u}} (f : W ⟶ X)
  (I T : LineBundle X) (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
  (a : SheafOfModules.unit X.ringCatSheaf ⟶
    (tensorLineBundle X T (dualLineBundle X I)).val)
  (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
  (E : (Modules.pullback f).obj (dualLineBundle X I).val ≅
    SheafOfModules.unit W.ringCatSheaf)
  (ha : pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle X I).val =
    tensorUnitSection (pullbackSectionMap f b) E.inv)

include ha in
/-- The same graph-twisted pole is coordinate times the same numerator on the
entire supplied boundary. This equation does not require the coordinate to be a unit. -/
theorem prescribed_pair_twistedIdealSection_eq_coordinate :
    pullbackSectionMap f (twistedIdealSection X I T φ b) =
      (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom) ≫
        pullbackSectionMap f a := by
  have : IsIso (pullbackTensorMap f T.val (dualLineBundle X I).val) :=
    PullbackTensor.Local.pullbackTensorMap_isIso f T.val (dualLineBundle X I).val T.property
  apply (cancel_mono (pullbackTensorMap f T.val (dualLineBundle X I).val)).mp
  rw [Category.assoc, ha]
  have h := tensorUnitSection_precomp (pullbackSectionMap f b) E.inv
    (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  exact (pullbackSectionMap_tensorUnitSection f b (canonicalDualHom X I.val φ)).trans h

include ha in
/-- The graph pole is a unit only after the original coordinate is proved a unit.
In E5 that proof comes from the actual parameter's disjointness from the marked locus. -/
theorem prescribed_pair_twistedIdealSection_isIso
    [IsIso (pullbackSectionMap f a)]
    [IsIso (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom)] :
    IsIso (pullbackSectionMap f (twistedIdealSection X I T φ b)) := by
  rw [prescribed_pair_twistedIdealSection_eq_coordinate f I T φ a b E ha]
  infer_instance

include ha in
/-- The original numerator over its graph-twisted pole has inverse-coordinate
boundary value. No new section or frame is introduced. -/
theorem prescribed_pair_ratio_eq_inverse_coordinate
    [IsIso (pullbackSectionMap f a)]
    [IsIso (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom)] :
    let := prescribed_pair_twistedIdealSection_isIso f I T φ a b E ha
    pullbackSectionMap f a ≫ inv (pullbackSectionMap f (twistedIdealSection X I T φ b)) =
      inv (pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom) := by
  dsimp only
  let := prescribed_pair_twistedIdealSection_isIso f I T φ a b E ha
  apply (cancel_mono (pullbackSectionMap f (twistedIdealSection X I T φ b))).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    prescribed_pair_twistedIdealSection_eq_coordinate f I T φ a b E ha,
    IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible
