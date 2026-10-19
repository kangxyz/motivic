/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Divisors.Order.IdealFrameOrderCancellation
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Multiplicity.ClosedImmersionPointCoefficient
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.CodimensionOneDominance
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Original closed-divisor coefficients cancel in the boundary frame

At a codimension-one point in the specified ideal frame, the actual stalk
quotient is Artinian. Hence any preimage in the original closed subscheme is
generic, and the existing fundamental-cycle formula applies without a supplied
genericity or coefficient equality. The rational correction cancels that exact
coefficient, including its full quotient length. Global support purity and
extension of the prescribed boundary frame are separate geometric steps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Order
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme

variable {C D : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (i : D ⟶ C) [IsClosedImmersion i]
  (hI : IsLocallyRankOne C (idealModule i)) (W : C.affineOpens) [Nonempty W.val]
  (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))

include hI e in
/-- Genericity is proved from the actual nonzero principal stalk equation,
not supplied as a premise of the fundamental-cycle comparison. -/
theorem mem_genericPoints_of_ideal_frame_coheight_one (y : D)
    (hyW : i y ∈ W.val) (hy : coheight (i y) = 1) : y ∈ genericPoints D := by
  have : IsNoetherian D := isNoetherian_of_finiteType i
  have : Ring.KrullDimLE 1 (C.presheaf.stalk (i y)) :=
    krullDimLE_of_coheight_le hy.le
  have hr : C.presheaf.germ W.val (i y) hyW (idealFrameScalar i W.val e) ≠ 0 :=
    (map_ne_zero_iff (C.presheaf.germ W.val (i y) hyW).hom
      (germ_injective_of_isIntegral C (i y) hyW)).mpr (idealFrameScalar_ne_zero i W.val e)
  have hlength : IsFiniteLength (C.presheaf.stalk (i y))
      ((C.presheaf.stalk (i y)) ⧸ i.ker.stalk (i y)) := by
    rw [ker_stalk_eq_span_idealFrameScalar i hI W e hyW]
    exact isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hlength
  have : IsArtinianRing ((C.presheaf.stalk (i y)) ⧸ i.ker.stalk (i y)) :=
    isArtinian_of_tower (C.presheaf.stalk (i y)) inferInstance
  have : IsArtinianRing (D.presheaf.stalk y) :=
    ((Ideal.quotEquivOfEq (i.ker_stalk y)).trans (stalkQuotientKerEquiv i y)).isArtinianRing
  have : Ring.KrullDimLE 0 (D.presheaf.stalk y) :=
    isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  apply mem_genericPoints_of_coheight_eq_zero
  have hd : ringKrullDim (D.presheaf.stalk y) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

include hI in
/-- The original pushed fundamental-cycle coefficient is canceled by the
rational frame ratio at every codimension-one point of the specified chart. -/
theorem fundamentalCoefficient_add_ord_unit_ratio_eq_zero
    (b : Γ(C, W.val)) (hb : IsUnit b) {x : C}
    (hxW : x ∈ W.val) (hx : coheight x = 1) :
    letI : IsNoetherian D := isNoetherian_of_finiteType i
    IntegralCycle.toPoints (IntegralCycle.finitePushforward i (fundamentalCycle D)) x +
      C.ord (C.germToFunctionField W.val b /
        C.germToFunctionField W.val (idealFrameScalar i W.val e)) x = 0 := by
  have : IsNoetherian D := isNoetherian_of_finiteType i
  have hg : ∀ y : D, i y = x → y ∈ genericPoints D := by
    intro y hy
    apply mem_genericPoints_of_ideal_frame_coheight_one i hI W e y
    · simpa only [hy] using hxW
    · simpa only [hy] using hx
  rw [closedImmersion_fundamentalCoefficient_eq_length_at i x hg]
  exact ideal_quotient_length_add_ord_unit_ratio_eq_zero i hI W e b hb hxW hx

end AlgebraicGeometry.Scheme
