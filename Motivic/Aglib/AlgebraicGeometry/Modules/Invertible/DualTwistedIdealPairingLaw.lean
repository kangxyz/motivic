module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealPairing
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualUnitFrame
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.RankOneReciprocity
/-! # The actual dual twisted ideal preserves its original evaluation pairing -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem dualTwistedIdeal_pairing_frame (X : Scheme.{u}) (I T : LineBundle X)
    (U : X.Opensᵒᵖ)
    (m : (tensorLineBundle X I (dualLineBundle X T)).val.val.obj U)
    (n n₀ : (tensorLineBundle X T (dualLineBundle X I)).val.val.obj U)
    (d : (dualLineBundle X (tensorLineBundle X T (dualLineBundle X I))).val.val.obj U)
    (h : d.val.app (op (Over.mk (𝟙 U.unop))) n₀ = (1 : X.presheaf.obj U)) :
    (((dualTwistedIdealIso X I T).hom.val.app U m).val.app
      (op (Over.mk (𝟙 U.unop)))) n =
    (twistedIdealPairingIso X I T).hom.val.app U
      ((tensorSheafUnit X _ _).app U (m ⊗ₜ n)) := by
  have he := dualTwistedIdealIso_apply_frame X I T U m n₀ d h
  have hn := dual_section_smul_exchange X (tensorLineBundle X T (dualLineBundle X I))
    U d n₀ n
  rw [h, one_smul] at hn
  rw [he]
  change X.presheaf.map (𝟙 U.unop).op
      ((twistedIdealPairingIso X I T).hom.val.app U
        ((tensorSheafUnit X _ _).app U (m ⊗ₜ n₀))) *
      (show X.presheaf.obj U from d.val.app (op (Over.mk (𝟙 U.unop))) n) = _
  simp only [op_id]
  have hid := X.presheaf.map_id (op U.unop)
  rw [hid]
  conv_rhs => rw [hn]
  rw [TensorProduct.tmul_smul, (tensorSheafUnit X _ _).app U |>.hom.map_smul,
    ((twistedIdealPairingIso X I T).hom.val.app U).hom.map_smul]
  change (show X.presheaf.obj U from (twistedIdealPairingIso X I T).hom.val.app U
    ((tensorSheafUnit X _ _).app U (m ⊗ₜ n₀))) * _ = _
  simp [mul_comm]

/-- The actual dual twisted ideal identification preserves the original evaluation pairing. -/
theorem dualTwistedIdealIso_pairing (X : Scheme.{u}) (I T : LineBundle X) :
    tensorSheafMap X (dualTwistedIdealIso X I T).hom
        (𝟙 (tensorLineBundle X T (dualLineBundle X I)).val) ≫
      (dualEvaluationIso X (tensorLineBundle X T (dualLineBundle X I))).hom =
    (twistedIdealPairingIso X I T).hom := by
  let M := tensorLineBundle X I (dualLineBundle X T)
  let N := tensorLineBundle X T (dualLineBundle X I)
  let O := SheafOfModules.unit X.ringCatSheaf
  let f := tensorSheafMap X (dualTwistedIdealIso X I T).hom (𝟙 N.val) ≫
    (dualEvaluationIso X N).hom
  let g := (twistedIdealPairingIso X I T).hom
  change f = g
  apply moduleTensor_hom_ext
  intro U m n
  let z := moduleTensorSection X M.val N.val U m n
  have hc : Presheaf.equalizerSieve (F := O.val.presheaf)
      (f.val.app (op U) z) (g.val.app (op U) z) ∈
      (Opens.grothendieckTopology X) U := by
    intro x hxU
    obtain ⟨W, hxW, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X N.val).mp N.property x
    let V : X.Opens := W ⊓ U
    let j : V ⟶ U := homOfLE inf_le_right
    let k : V ⟶ W := homOfLE inf_le_left
    refine ⟨V, j, ?_, ⟨hxW, hxU⟩⟩
    change O.val.map j.op (f.val.app (op U) z) = O.val.map j.op (g.val.app (op U) z)
    have hf := _root_.PresheafOfModules.naturality_apply f.val j.op z
    have hg := _root_.PresheafOfModules.naturality_apply g.val j.op z
    erw [← hf, ← hg]
    change f.val.app (op V)
      (((moduleTensorLeftFunctor X M.val).obj N.val).presheaf.map j.op z) =
      g.val.app (op V)
        (((moduleTensorLeftFunctor X M.val).obj N.val).presheaf.map j.op z)
    rw [moduleTensorSection_restrict]
    let m' := M.val.val.map j.op m
    let n' := N.val.val.map j.op n
    let n₀ := e.inv.val.app (op (Over.mk k)) (1 : Γ(X, V))
    let d := (dualLocalIso X N.val W e).inv.val.app (op (Over.mk k)) (1 : Γ(X, V))
    have hd : d.val.app (op (Over.mk (𝟙 V))) n₀ = (1 : Γ(X, V)) :=
      dual_unit_frame_evaluation X N W e (op (Over.mk k))
    change (dualEvaluationIso X N).hom.val.app (op V)
      ((tensorSheafMap X (dualTwistedIdealIso X I T).hom (𝟙 N.val)).val.app (op V)
        ((tensorSheafUnit X M.val N.val).app (op V) (m' ⊗ₜ n'))) =
      g.val.app (op V) ((tensorSheafUnit X M.val N.val).app (op V) (m' ⊗ₜ n'))
    rw [tensorSheafMap_tmul, dualEvaluationIso_hom_tmul]
    exact dualTwistedIdeal_pairing_frame X I T (op V) m' n' n₀ d hd
  apply O.isSheaf.isSeparated U _ hc
  intro V j hj
  exact hj
end AlgebraicGeometry.Scheme.Modules.Invertible
