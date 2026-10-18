/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IdealFrameMovedCycle
public import Motivic.AlgebraicGeometry.Cycles.CodimensionOneDominance

/-! # Component dominance of the literal moved sum -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace Motivic

/-- A finite codimension-one whole support in the retained smooth relative curve
dominates an actual base component. No flatness or no-vertical premise is used. -/
theorem finitePointSupport_dominates_component {C S V : Scheme.{u}}
    (q : C ⟶ S) [IsSeparated q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (x : C) (hx1 : coheight x = 1)
    (hretained : Set.range (IntegralClosedSubscheme.pointClosure x).val.subschemeι ⊆
      Set.range j)
    [IsFinite ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q)] :
    Set.range ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q) ∈
      irreducibleComponents S := by
  let D := IntegralClosedSubscheme.pointClosure x
  let d := D.val.subschemeι
  have hd : Set.range d ⊆ Set.range j := hretained
  let i := IsOpenImmersion.lift j d hd
  have hi : i ≫ j = d := IsOpenImmersion.lift_fac j d hd
  have : IsClosedImmersion (i ≫ j) := by rw [hi]; infer_instance
  have : IsClosedImmersion i := IsClosedImmersion.of_comp i j
  have hcomp : i ≫ (j ≫ q) = d ≫ q := by rw [← Category.assoc, hi]
  have : IsFinite (i ≫ (j ≫ q)) := by rw [hcomp]; infer_instance
  let a := genericPoint D.val.subscheme
  have hda : d a = x := IntegralClosedSubscheme.point_pointClosure x
  have ha : coheight (i a) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion j]
    change coheight ((i ≫ j) a) = 1
    rw [hi, hda]
    exact hx1
  have hg := image_mem_genericPoints_of_coheight_one_finite_closed_support i (j ≫ q) a ha
  have hga : (j ≫ q) (i a) = (d ≫ q) a :=
    congrArg (fun f : D.val.subscheme ⟶ S => f a) hcomp
  rw [hga] at hg
  have he : closure ({(d ≫ q) a} : Set S) = Set.range (d ≫ q) := by
    simpa only [Set.image_univ, (d ≫ q).isClosedMap.isClosed_range.closure_eq] using
      ((genericPoint_spec D.val.subscheme).image (d ≫ q).continuous).def
  rwa [genericPoints, Set.mem_ofPred_eq, he] at hg

variable {C D : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (i : D ⟶ C) [IsClosedImmersion i] (hI : IsLocallyRankOne C (idealModule i))
  (W : C.affineOpens) [Nonempty W.val]
  (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
  (b : Γ(C, W.val)) (hb : IsUnit b)

include hI

/-- Both summands vanish off codimension one: purity of the actual invertible
ideal handles the fundamental cycle, while native order handles its correction. -/
theorem idealFrameMovedCycle_coheight_one (x : C)
    (hx : idealFrameMovedCycle i W e b hb x ≠ 0) : coheight x = 1 := by
  have : IsNoetherian D := isNoetherian_of_finiteType i
  by_contra hn
  apply hx
  rw [idealFrameMovedCycle_apply,
    closedImmersion_fundamentalCoefficient_eq_zero_at i x (by
      intro y hy hgeneric
      apply hn
      simpa only [hy] using coheight_image_generic_of_invertible_ideal i hI y hgeneric),
    Scheme.ord_eq_zero_of_coheight_neq_one hn, add_zero]

/-- Actual finite moved supports dominate components of the original base. -/
theorem idealFrameMovedCycle_support_dominates_component
    {S V : Scheme.{u}} [IsAffine S] [V.IsQuasiAffine]
    (q : C ⟶ S) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hW : (Set.range j)ᶜ ⊆ (W.val : Set C)) (x : C)
    (hx : idealFrameMovedCycle i W e b hb x ≠ 0) :
    Set.range ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q) ∈
      irreducibleComponents S := by
  have : IsFinite ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q) :=
    idealFrameMovedCycle_support_isFinite i W e b hb hI q j hW x hx
  apply finitePointSupport_dominates_component q j x
    (idealFrameMovedCycle_coheight_one i hI W e b hb x hx)
  rw [Scheme.IdealSheafData.range_subschemeι, IntegralClosedSubscheme.support_pointClosure]
  intro y hy
  by_contra hn
  exact idealFrameMovedCycle_support_closure i W e b hb hI x hx hy (hW hn)

end Motivic
