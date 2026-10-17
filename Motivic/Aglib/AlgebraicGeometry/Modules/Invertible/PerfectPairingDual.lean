module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DualTwistedIdealPairingLaw
/-! # The canonical dual comparison supplied by an actual perfect line pairing -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- An actual perfect pairing canonically identifies its first line with the dual. -/
def perfectPairingDualIso (X : Scheme.{u}) (M N : LineBundle X)
    (q : tensorSheaf X M.val N.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    M.val ≅ (dualLineBundle X N).val :=
  (tensorSheafRightUnit X M.val).symm ≪≫
    tensorSheafIso X (Iso.refl M.val)
      (tensorSheafBraiding X N.val (dualLineBundle X N).val ≪≫
        dualEvaluationIso X N).symm ≪≫
    (tensorLineBundleAssociator X M N (dualLineBundle X N)).symm ≪≫
    tensorSheafIso X q (Iso.refl (dualLineBundle X N).val) ≪≫
    tensorSheafLeftUnit X (dualLineBundle X N).val

/-- The globally constructed iso has the prescribed formula in every actual dual unit frame. -/
theorem perfectPairingDualIso_apply_frame (X : Scheme.{u}) (M N : LineBundle X)
    (q : tensorSheaf X M.val N.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opensᵒᵖ)
    (m : M.val.val.obj U)
    (n : N.val.val.obj U)
    (d : (dualLineBundle X N).val.val.obj U)
    (h : d.val.app (op (Over.mk (𝟙 U.unop))) n = (1 : X.presheaf.obj U)) :
    (perfectPairingDualIso X M N q).hom.val.app U m =
      (q).hom.val.app U
        ((tensorSheafUnit X _ _).app U (m ⊗ₜ n)) • d := by
  let D := dualLineBundle X N
  let eN := tensorSheafBraiding X N.val D.val ≪≫ dualEvaluationIso X N
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
private theorem perfectPairing_pairing_frame (X : Scheme.{u}) (M N : LineBundle X)
    (q : tensorSheaf X M.val N.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opensᵒᵖ)
    (m : M.val.val.obj U)
    (n n₀ : N.val.val.obj U)
    (d : (dualLineBundle X N).val.val.obj U)
    (h : d.val.app (op (Over.mk (𝟙 U.unop))) n₀ = (1 : X.presheaf.obj U)) :
    (((perfectPairingDualIso X M N q).hom.val.app U m).val.app
      (op (Over.mk (𝟙 U.unop)))) n =
    (q).hom.val.app U
      ((tensorSheafUnit X _ _).app U (m ⊗ₜ n)) := by
  have he := perfectPairingDualIso_apply_frame X M N q U m n₀ d h
  have hn := dual_section_smul_exchange X N
    U d n₀ n
  rw [h, one_smul] at hn
  rw [he]
  change X.presheaf.map (𝟙 U.unop).op
      ((q).hom.val.app U
        ((tensorSheafUnit X _ _).app U (m ⊗ₜ n₀))) *
      (show X.presheaf.obj U from d.val.app (op (Over.mk (𝟙 U.unop))) n) = _
  simp only [op_id]
  have hid := X.presheaf.map_id (op U.unop)
  rw [hid]
  conv_rhs => rw [hn]
  rw [TensorProduct.tmul_smul, (tensorSheafUnit X _ _).app U |>.hom.map_smul,
    ((q).hom.val.app U).hom.map_smul]
  change (show X.presheaf.obj U from (q).hom.val.app U
    ((tensorSheafUnit X _ _).app U (m ⊗ₜ n₀))) * _ = _
  simp [mul_comm]

/-- The actual dual twisted ideal identification preserves the original evaluation pairing. -/
theorem perfectPairingDualIso_pairing (X : Scheme.{u}) (M N : LineBundle X)
    (q : tensorSheaf X M.val N.val ≅ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap X (perfectPairingDualIso X M N q).hom
        (𝟙 N.val) ≫
      (dualEvaluationIso X N).hom =
    (q).hom := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let f := tensorSheafMap X (perfectPairingDualIso X M N q).hom (𝟙 N.val) ≫
    (dualEvaluationIso X N).hom
  let g := (q).hom
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
      ((tensorSheafMap X (perfectPairingDualIso X M N q).hom (𝟙 N.val)).val.app (op V)
        ((tensorSheafUnit X M.val N.val).app (op V) (m' ⊗ₜ n'))) =
      g.val.app (op V) ((tensorSheafUnit X M.val N.val).app (op V) (m' ⊗ₜ n'))
    rw [tensorSheafMap_tmul, dualEvaluationIso_hom_tmul]
    exact perfectPairing_pairing_frame X M N q (op V) m' n' n₀ d hd
  apply O.isSheaf.isSeparated U _ hc
  intro V j hj
  exact hj
end AlgebraicGeometry.Scheme.Modules.Invertible
