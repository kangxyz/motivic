/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.Graph

/-! # Whole-infinity graph pencil interface and trust checks -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible

universe u

variable {X W : Scheme.{u}} (f : W ⟶ X) (I T : LineBundle X)
    (φ : I.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorLineBundle X T (dualLineBundle X I)).val)
    (b : SheafOfModules.unit X.ringCatSheaf ⟶ T.val)
    (E : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (dualLineBundle X I).val ≅
      SheafOfModules.unit W.ringCatSheaf)

variable (ha : Eq
      (α := SheafOfModules.Hom (SheafOfModules.unit W.ringCatSheaf)
        (tensorSheaf W ((AlgebraicGeometry.Scheme.Modules.pullback f).obj T.val)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (dualLineBundle X I).val)))
      (pullbackSectionMap f a ≫ pullbackTensorMap f T.val (dualLineBundle X I).val)
      (tensorUnitSection (X := W)
        (M := (AlgebraicGeometry.Scheme.Modules.pullback f).obj T.val)
        (N := (AlgebraicGeometry.Scheme.Modules.pullback f).obj (dualLineBundle X I).val)
        (pullbackSectionMap f b) E.inv))

variable (hE : pullbackSectionMap f (canonicalDualHom X I.val φ) ≫ E.hom = 𝟙 _)

example :
    pullbackSectionMap f a =
      pullbackSectionMap f (twistedIdealSection X I T φ b) :=
  prescribed_pair_eq_twistedIdealSection f I T φ a b E ha hE

open Lean in
run_cmd do
  for name in #[``prescribed_pair_eq_twistedIdealSection,
      ``Scheme.RelativeCurvePencil.graphSections_infinity_eq,
      ``Scheme.RelativeCurvePencil.graphFunctionals_infinity_eq,
      ``Scheme.RelativeCurvePencil.graphTwistedSection_infinity_isIso,
      ``Motivic.PresheafWithTransfers.transfer_graphTwistedSections_sub_eq_graph,
      ``Scheme.RelativeCurvePencil.transfer_dataOfBoundarySections_lam_comp_graph_eq_id] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The original graph section pencil uses only standard foundations."
