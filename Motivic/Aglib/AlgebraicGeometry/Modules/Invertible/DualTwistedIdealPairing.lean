module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealEvaluation
/-! # Evaluation of the actual dual twisted ideal identification -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The actual inverse evaluation in a supplied dual unit frame. -/
theorem inverseEvaluation_unit_frame (X : Scheme.{u}) (N : LineBundle X)
    (U : X.Opensᵒᵖ) (n : N.val.val.obj U) (d : (dualLineBundle X N).val.val.obj U)
    (h : d.val.app (op (Over.mk (𝟙 U.unop))) n = (1 : X.presheaf.obj U)) :
    (tensorSheafBraiding X N.val (dualLineBundle X N).val ≪≫
      dualEvaluationIso X N).inv.val.app U (1 : X.presheaf.obj U) =
    (tensorSheafUnit X N.val (dualLineBundle X N).val).app U (n ⊗ₜ d) := by
  let e := tensorSheafBraiding X N.val (dualLineBundle X N).val ≪≫ dualEvaluationIso X N
  have he : e.hom.val.app U
      ((tensorSheafUnit X N.val (dualLineBundle X N).val).app U (n ⊗ₜ d)) =
        (1 : X.presheaf.obj U) := by
    change (dualEvaluationIso X N).hom.val.app U
      ((tensorSheafBraiding X N.val (dualLineBundle X N).val).hom.val.app U _) = _
    rw [tensorSheafBraiding_hom_tmul, dualEvaluationIso_hom_tmul, h]
  rw [← he]
  exact congrArg (fun f => f.val.app U
    ((tensorSheafUnit X N.val (dualLineBundle X N).val).app U (n ⊗ₜ d))) e.hom_inv_id

/-- The globally constructed iso has the prescribed formula in every actual dual unit frame. -/
theorem dualTwistedIdealIso_apply_frame (X : Scheme.{u}) (I T : LineBundle X)
    (U : X.Opensᵒᵖ)
    (m : (tensorLineBundle X I (dualLineBundle X T)).val.val.obj U)
    (n : (tensorLineBundle X T (dualLineBundle X I)).val.val.obj U)
    (d : (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val.val.obj U)
    (h : d.val.app (op (Over.mk (𝟙 U.unop))) n = (1 : X.presheaf.obj U)) :
    (dualTwistedIdealIso X I T).hom.val.app U m =
      (twistedIdealPairingIso X I T).hom.val.app U
        ((tensorSheafUnit X _ _).app U (m ⊗ₜ n)) • d := by
  let M := tensorLineBundle X I (dualLineBundle X T)
  let N := tensorLineBundle X T (dualLineBundle X I)
  let D := dualLineBundle X N
  let eN := tensorSheafBraiding X N.val D.val ≪≫ dualEvaluationIso X N
  let q := twistedIdealPairingIso X I T
  change (tensorSheafLeftUnit X D.val).hom.val.app U
    ((tensorSheafMap X q.hom (𝟙 D.val)).val.app U
      ((tensorLineBundleAssociator X M N D).inv.val.app U
        ((tensorSheafMap X (𝟙 M.val) eN.inv).val.app U
          ((tensorSheafRightUnit X M.val).inv.val.app U m)))) = _
  rw [tensorSheafRightUnit_inv_apply, tensorSheafMap_tmul]
  have hn := inverseEvaluation_unit_frame X N U n d h
  change eN.inv.val.app U (1 : X.presheaf.obj U) = _ at hn
  rw [hn]
  change (tensorSheafLeftUnit X D.val).hom.val.app U
    ((tensorSheafMap X q.hom (𝟙 D.val)).val.app U
      ((tensorLineBundleAssociator X M N D).inv.val.app U
        ((tensorSheafUnit X M.val (tensorSheaf X N.val D.val)).app U
          (m ⊗ₜ (tensorSheafUnit X N.val D.val).app U (n ⊗ₜ d))))) = _
  rw [tensorLineBundleAssociator_inv_tmul, tensorSheafMap_tmul, tensorSheafLeftUnit_tmul]
  rfl
end AlgebraicGeometry.Scheme.Modules.Invertible
