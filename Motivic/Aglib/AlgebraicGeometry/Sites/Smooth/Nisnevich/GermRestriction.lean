/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.CommonGerms

/-! # Detecting original germs on actual residue-isomorphic étale restrictions -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {X U : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- Vanishing of the original germ after a displayed pointed étale restriction
implies vanishing of the original germ before restriction. -/
theorem germ_eq_zero_of_restricted_germ_eq_zero (g : U ⟶ X) [Etale g.left]
    (u : U.left) [IsIso (g.left.residueFieldMap u)] (s : F.obj (op X))
    (hs : sectionToNisnevichPoint F U u (F.map g.op s) = 0) :
    sectionToNisnevichPoint F X (g.left u) s = 0 := by
  obtain ⟨R, hR⟩ := (sectionToNisnevichPoint_eq_zero_iff F _).mp hs
  let h := R.toBase ≫ g
  let : Etale h.left := by
    change Etale (R.toBase.left ≫ g.left)
    infer_instance
  have hc : h.left R.center = g.left u := by
    change g.left (R.obj.obj.hom R.center) = g.left u
    rw [show R.obj.obj.hom R.center = u from R.toBase_center]
  let : IsIso (h.left.residueFieldMap R.center) := by
    change IsIso ((R.toBase.left ≫ g.left).residueFieldMap R.center)
    rw [Scheme.residueFieldMap_comp]
    have : IsIso (g.left.residueFieldMap (R.toBase.left R.center)) := by
      change IsIso (g.left.residueFieldMap (R.obj.obj.hom R.center))
      rw [show R.obj.obj.hom R.center = u from R.toBase_center]
      infer_instance
    infer_instance
  apply germ_eq_zero_of_pointed_restriction F h R.center hc s
  simpa only [h, op_comp, F.map_comp, ConcreteCategory.comp_apply] using hR

/-- Equal restricted germs detect equality in the original point-fiber colimit. -/
theorem germs_eq_of_restricted_germs_eq (g : U ⟶ X) [Etale g.left]
    (u : U.left) [IsIso (g.left.residueFieldMap u)] (s t : F.obj (op X))
    (hst : sectionToNisnevichPoint F U u (F.map g.op s) =
      sectionToNisnevichPoint F U u (F.map g.op t)) :
    sectionToNisnevichPoint F X (g.left u) s =
      sectionToNisnevichPoint F X (g.left u) t := by
  have hz := germ_eq_zero_of_restricted_germ_eq_zero.{u, v} F g u (s - t)
    (by simp only [map_sub, hst, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

end AlgebraicGeometry.Scheme.SmoothSite
