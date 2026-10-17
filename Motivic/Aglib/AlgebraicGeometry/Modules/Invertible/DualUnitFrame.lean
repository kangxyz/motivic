module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.TensorLineBundleSections
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization
/-! # Original dual unit frames evaluate to one -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

theorem dual_unit_frame_evaluation (X : Scheme.{u}) (N : LineBundle X) (U : X.Opens)
    (e : N.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : (Over U)ᵒᵖ) :
    (((dualLocalIso X N.val U e).inv.val.app V (1 : Γ(X, V.unop.left))).val.app
      (op (Over.mk (𝟙 V.unop.left))))
      (e.inv.val.app V (1 : Γ(X, V.unop.left))) = (1 : Γ(X, V.unop.left)) := by
  let d := (dualLocalIso X N.val U e).inv.val.app V (1 : Γ(X, V.unop.left))
  let n := e.inv.val.app V (1 : Γ(X, V.unop.left))
  have h := congrArg (fun k => k.app V (d ⊗ₜ[Γ(X, V.unop.left)] n))
    (dualEvaluationLocalIso_hom X N.val U e)
  change (show Γ(X, V.unop.left) from (dualLocalIso X N.val U e).hom.val.app V d) *
      (show Γ(X, V.unop.left) from e.hom.val.app V n) =
    d.val.app (op (Over.mk (𝟙 V.unop.left))) n at h
  have hd : (dualLocalIso X N.val U e).hom.val.app V d = (1 : Γ(X, V.unop.left)) :=
    congrArg (fun k => k.val.app V (1 : Γ(X, V.unop.left)))
      (dualLocalIso X N.val U e).inv_hom_id
  have hn : e.hom.val.app V n = (1 : Γ(X, V.unop.left)) :=
    congrArg (fun k => k.val.app V (1 : Γ(X, V.unop.left))) e.inv_hom_id
  rw [hd, hn, mul_one] at h
  exact h.symm
end AlgebraicGeometry.Scheme.Modules.Invertible
