/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.FiniteSupportLocality

/-!
# Finite-support locality at arbitrary scheme points

Choose an actual zero representative at each target of the selected finite
source fiber. The existing family factorization supplies a zero restriction
of the transferred section. No closedness of the source or target points is
needed, and specializing centers need not be removed from one another.

This concerns existing sections and the original signed Cor action. It does
not identify different lifts of arbitrary tuples of germs or construct the
all-point acyclic transfer envelope.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

/-- A zero germ at every target of the actual finite source fiber gives a
zero transferred germ, at an arbitrary source point. -/
theorem generator_transfer_germ_eq_zero_at_point
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (x : X.left) (s : P.sections (Cor.mk Y))
    (hs : ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
        Y (A.targetProjection z) s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
      X x (P.transfer A.cycle s) = 0 := by
  classical
  let I := {a : A.scheme // A.projection a = x}
  have hrep (a : I) := (SmoothSite.sectionToNisnevichPoint_eq_zero_iff.{u, v}
    ((toPresheaf k).obj P) (X := Y) (x := A.targetProjection a.val) s).mp (hs a.val a.property)
  choose R hR using hrep
  let V (a : I) :=
    (SmoothSite.nisnevichNeighborhoodFunctor Y (A.targetProjection a.val)).obj (R a)
  let q (a : I) : V a ⟶ Y := (R a).toBase
  have hqEt : ∀ a, Etale (q a).left := by intro a; dsimp [q]; infer_instance
  have hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (a : I) (w : (V a).left), (q a).left w = A.targetProjection z ∧
        IsIso ((q a).left.residueFieldMap w) := by
    intro z hz
    let a : I := ⟨z, hz⟩
    exact ⟨a, (R a).center, (R a).toBase_center, inferInstance⟩
  apply (SmoothSite.sectionToNisnevichPoint_eq_zero_iff _ _).mpr
  exact @exists_restriction_transfer_eq_zero_of_family _ _ P X Y A x I V q
    hqEt hq s hR

/-- Finite-support germ locality for an arbitrary signed correspondence.
All integer coefficients and cancellations are those of the original correspondence group. -/
theorem transfer_germ_eq_zero_at_point
    (α : FiniteCorrespondence X.hom Y.hom)
    (x : X.left) (s : P.sections (Cor.mk Y))
    (hs : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
        Y (A.targetProjection z) s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P)
      X x (P.transfer α s) = 0 := by
  classical
  let ι : P.sections (Cor.mk X) ⟶
      ((SmoothSite.nisnevichPoint X x).presheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((toPresheaf k).obj P) :=
    SmoothSite.sectionToNisnevichPoint.{u, v} ((toPresheaf k).obj P) X x
  let L : (Cor.mk X ⟶ Cor.mk Y) →+
      ((SmoothSite.nisnevichPoint X x).presheafFiber (A := AddCommGrpCat.{max (u + 1) v})).obj
        ((toPresheaf k).obj P) :=
    { toFun := fun γ ↦ ι (P.transfer γ s)
      map_zero' := by simp
      map_add' := fun γ δ ↦ by
        simp only [transfer_add, AddCommGrpCat.hom_add_apply, map_add] }
  have hα : ∑ A ∈ α.support, α A • A.cycle = α := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using α.sum_single
  change L α = 0
  rw [← hα, map_sum]
  apply Finset.sum_eq_zero
  intro A hA
  rw [map_zsmul]
  have hA0 : L A.cycle = 0 := generator_transfer_germ_eq_zero_at_point k P A x s (hs A hA)
  rw [hA0, smul_zero]

/-- Existing sections with the same finitely relevant target germs have the same
source germ after the original signed transfer. -/
theorem transfer_germ_eq_at_point_of_eq_on_support
    (α : FiniteCorrespondence X.hom Y.hom)
    (x : X.left) (s t : P.sections (Cor.mk Y))
    (hst : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y (A.targetProjection z) s =
        SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y (A.targetProjection z) t) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α t) := by
  have hzero := transfer_germ_eq_zero_at_point k P α x (s - t) (by
    intro A hA z hz
    rw [map_sub, hst A hA z hz, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)


end Motivic.PresheafWithTransfers
