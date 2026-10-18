/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IdealFrameCancellation
public import Mathlib.RingTheory.KrullDimension.Regular
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Purity and whole-chart cancellation of the original Cartier support

Generic points of the original closed subscheme map to codimension-one points
of the integral ambient scheme. The proof uses the actual principal stalk
quotient and its regular-element dimension formula. Consequently the original
fundamental coefficient plus the rational frame correction vanishes at every
point of the prescribed frame chart, not only at codimension-one points.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace Motivic

variable {C D : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (i : D ⟶ C) [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i))

include hI

/-- An original generic closed-divisor point has ambient codimension one,
computed from its exact frame scalar and its actual stalk quotient. -/
theorem coheight_image_generic_of_ideal_frame
    (W : C.affineOpens) [Nonempty W.val]
    (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
    (y : D) (hy : y ∈ genericPoints D) (hyW : i y ∈ W.val) : coheight (i y) = 1 := by
  have : IsNoetherian D := isNoetherian_of_finiteType i
  let r : C.presheaf.stalk (i y) :=
    C.presheaf.germ W.val (i y) hyW (idealFrameScalar i W.val e)
  have hr : r ≠ 0 :=
    (map_ne_zero_iff (C.presheaf.germ W.val (i y) hyW).hom
      (germ_injective_of_isIntegral C (i y) hyW)).mpr (idealFrameScalar_ne_zero i W.val e)
  have hk : i.ker.stalk (i y) = Ideal.span {r} :=
    ker_stalk_eq_span_idealFrameScalar i hI W e hyW
  let E : ((C.presheaf.stalk (i y)) ⧸ Ideal.span {r}) ≃+* D.presheaf.stalk y :=
    (Ideal.quotEquivOfEq (hk.symm.trans (i.ker_stalk y))).trans (stalkQuotientKerEquiv i y)
  have : IsArtinianRing (D.presheaf.stalk y) := isArtinianRing_stalk_of_mem_genericPoints y hy
  have : IsArtinianRing ((C.presheaf.stalk (i y)) ⧸ Ideal.span {r}) := E.symm.isArtinianRing
  have : Nontrivial ((C.presheaf.stalk (i y)) ⧸ Ideal.span {r}) := E.toEquiv.nontrivial
  have : Ring.KrullDimLE 0 ((C.presheaf.stalk (i y)) ⧸ Ideal.span {r}) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  have hdim : ringKrullDim ((C.presheaf.stalk (i y)) ⧸ Ideal.span {r}) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hzero : (i.stalkMap y).hom r = 0 := by
    change r ∈ RingHom.ker (i.stalkMap y).hom
    rw [← i.ker_stalk, hk]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hnu : ¬ IsUnit r := fun hu => (hu.map (i.stalkMap y).hom).ne_zero hzero
  have hjac : r ∈ Ring.jacobson (C.presheaf.stalk (i y)) := by
    rwa [IsLocalRing.ringJacobson_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    (IsSMulRegular.of_ne_zero hr) hjac
  rw [hdim, zero_add, ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd.symm

/-- Purity uses local frames supplied by the original invertible ideal itself;
no global trivialization is assumed. -/
theorem coheight_image_generic_of_invertible_ideal (y : D) (hy : y ∈ genericPoints D) :
    coheight (i y) = 1 := by
  obtain ⟨W, hyW, ⟨e⟩⟩ :=
    (isLocallyRankOne_iff_local_unit C (idealModule i)).mp hI (i y)
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open hyW W.isOpen
  have : Nonempty V := ⟨⟨i y, hyV⟩⟩
  exact coheight_image_generic_of_ideal_frame i hI ⟨V, hV⟩
    (restrictOverUnitIso C (idealModule i) (homOfLE hVW) e) y hy hyV

/-- The SUM vanishes on the whole original frame neighborhood, including points
where the canonical section vanishes and points of other codimensions. -/
theorem fundamentalCoefficient_add_ord_unit_ratio_eq_zero_on_frame
    (W : C.affineOpens) [Nonempty W.val]
    (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
    (b : Γ(C, W.val)) (hb : IsUnit b) {x : C} (hxW : x ∈ W.val) :
    letI : IsNoetherian D := isNoetherian_of_finiteType i
    IntegralCycle.toPoints (IntegralCycle.finitePushforward i (fundamentalCycle D)) x +
      C.ord (C.germToFunctionField W.val b /
        C.germToFunctionField W.val (idealFrameScalar i W.val e)) x = 0 := by
  have : IsNoetherian D := isNoetherian_of_finiteType i
  by_cases hx : coheight x = 1
  · exact fundamentalCoefficient_add_ord_unit_ratio_eq_zero i hI W e b hb hxW hx
  · rw [closedImmersion_fundamentalCoefficient_eq_zero_at i x (by
      intro y hy hgeneric
      apply hx
      simpa only [hy] using coheight_image_generic_of_invertible_ideal i hI y hgeneric),
      Scheme.ord_eq_zero_of_coheight_neq_one hx, add_zero]

end Motivic
