/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.PersistentFiniteSubfamily
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.SectionDetection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Germs.Pullback
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.CommonGerms

/-! # Actual sections with zero persistent germs vanish after an actual base shrinking

This is degree-zero detection only. No assertion about higher cohomology or
injective cokernels preserving the support condition is made.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherian S]
  {X U : SmoothSite S} (g : U ⟶ X) (x : X.left)
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  (hF : Presheaf.IsSheaf (nisnevichTopology S) F)
include hF

/-- Actual zero germs at all persistent points kill a section on the pullback of
an actual open neighborhood of the center. No cohomological descent is assumed. -/
theorem exists_open_restriction_eq_zero_of_persistent_germs (s : F.obj (op U))
    (hs : ∀ z : U.left, g.left z ⤳ x → sectionToNisnevichPoint.{u, 0} F U z s = 0) :
    ∃ W : X.left.Opens, x ∈ W ∧
      F.map (openInclusion U (g.left ⁻¹ᵁ W)).op s = 0 := by
  classical
  let I := {z : U.left // g.left z ⤳ x}
  choose N hN using fun z : I =>
    (sectionToNisnevichPoint_eq_zero_iff.{u, 0} F s).mp (hs z.val z.property)
  let V : I → SmoothSite S := fun z => (nisnevichNeighborhoodFunctor U z.val).obj (N z)
  let q : ∀ z, V z ⟶ U := fun z => (N z).toBase
  have hq : ∀ z : U.left, g.left z ⤳ x → ∃ (i : I) (y : (V i).left),
      (q i).left y = z ∧ IsIso ((q i).left.residueFieldMap y) := by
    intro z hz
    exact ⟨⟨z, hz⟩, (N ⟨z, hz⟩).center, (N ⟨z, hz⟩).toBase_center, inferInstance⟩
  obtain ⟨W, hxW, t, ht⟩ := Nisnevich.exists_open_finset_persistent_residueFieldLifting
    g.left x (fun i => (q i).left) hq
  refine ⟨W, hxW, ?_⟩
  let o := openInclusion U (g.left ⁻¹ᵁ W)
  apply section_eq_zero_of_original_germs F hF _
  intro z
  have hzW : g.left (o.left z) ∈ W := z.property
  obtain ⟨i, _, y, hy, hiy⟩ := ht (o.left z) hzW
  let := hiy
  have hz : sectionToNisnevichPoint.{u, 0} F U (o.left z) s = 0 :=
    germ_eq_zero_of_pointed_restriction.{u, 0} F (q i) y hy s (hN i)
  have hn := ConcreteCategory.congr_hom
    (sectionToNisnevichPoint_originalGermPullback.{u, 0} F o z) s
  change originalGermPullback.{u, 0} F o z (sectionToNisnevichPoint.{u, 0} F U (o.left z) s) =
    sectionToNisnevichPoint.{u, 0} F _ z (F.map o.op s) at hn
  rw [hz, map_zero] at hn
  exact hn.symm

end AlgebraicGeometry.Scheme.SmoothSite
