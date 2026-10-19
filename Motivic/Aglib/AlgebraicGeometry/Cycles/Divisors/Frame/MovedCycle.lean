/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.Frame.Support
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.PrincipalOrder

/-!
# The actual boundary-avoiding sum in an extended ideal frame

This is the original pushed closed-divisor fundamental cycle plus the native
order cycle of the rational frame ratio. An auxiliary unit open proves only
finiteness of the order support. Whole-boundary avoidance instead follows from
coefficient cancellation on the entire prescribed frame neighborhood. Every
nonzero coefficient's entire closed support then avoids the boundary and is
finite over the unchanged affine parameter base.
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
  (i : D ⟶ C) [IsClosedImmersion i] (W : C.affineOpens) [Nonempty W.val]
  (e : (idealModule i).over W.val ≅ SheafOfModules.unit (C.ringCatSheaf.over W.val))
  (b : Γ(C, W.val)) (hb : IsUnit b)

omit [IsClosedImmersion i] in
include hb in
/-- Only finite support is extracted from an auxiliary unit-open representation;
that auxiliary open need not contain any prescribed boundary point. -/
theorem finite_support_idealFrameRatio :
    (Function.support (C.ord (C.germToFunctionField W.val b /
      C.germToFunctionField W.val (idealFrameScalar i W.val e)))).Finite := by
  have hr : C.germToFunctionField W.val (idealFrameScalar i W.val e) ≠ 0 :=
    (map_ne_zero_iff (C.germToFunctionField W.val).hom
      (C.germToFunctionField_injective W.val)).mpr (idealFrameScalar_ne_zero i W.val e)
  have hf := div_ne_zero (hb.map (C.germToFunctionField W.val).hom).ne_zero hr
  obtain ⟨V, _, f, hV, he, hu⟩ := exists_isUnit_germ_eq C _ hf
  have : Nonempty V := hV
  simpa only [he] using C.finite_support_ord_of_unit_on_open V f hu

/-- The literal sum, retaining the original fundamental coefficients and native
orders, rather than an assumed boundary-avoiding replacement cycle. -/
def idealFrameMovedCycle : FiniteSupportCycle C :=
  letI : IsNoetherian D := isNoetherian_of_finiteType i
  IntegralCycle.toPoints (IntegralCycle.finitePushforward i (fundamentalCycle D)) +
    Finsupp.ofSupportFinite (C.ord (C.germToFunctionField W.val b /
      C.germToFunctionField W.val (idealFrameScalar i W.val e)))
      (finite_support_idealFrameRatio i W e b hb)

@[simp]
theorem idealFrameMovedCycle_apply (x : C) :
    idealFrameMovedCycle i W e b hb x =
      letI : IsNoetherian D := isNoetherian_of_finiteType i
      IntegralCycle.toPoints (IntegralCycle.finitePushforward i (fundamentalCycle D)) x +
        C.ord (C.germToFunctionField W.val b /
          C.germToFunctionField W.val (idealFrameScalar i W.val e)) x := rfl

/-- Cancellation occurs on the full prescribed frame chart, not the auxiliary
unit open used only to prove finite support of the rational correction. -/
theorem idealFrameMovedCycle_eq_zero_on_frame
    (hI : IsLocallyRankOne C (idealModule i)) {x : C} (hx : x ∈ W.val) :
    idealFrameMovedCycle i W e b hb x = 0 :=
  fundamentalCoefficient_add_ord_unit_ratio_eq_zero_on_frame i hI W e b hb hx

/-- The entire closure of every nonzero coefficient avoids the original frame
neighborhood; avoiding just its generic point is not substituted. -/
theorem idealFrameMovedCycle_support_closure
    (hI : IsLocallyRankOne C (idealModule i)) (x : C)
    (hx : idealFrameMovedCycle i W e b hb x ≠ 0) :
    closure ({x} : Set C) ⊆ (W.val : Set C)ᶜ := by
  apply closure_minimal _ W.val.isOpen.isClosed_compl
  exact Set.singleton_subset_iff.mpr fun hm =>
    hx (idealFrameMovedCycle_eq_zero_on_frame i W e b hb hI hm)

/-- The whole original integral support of a nonzero coefficient is finite over
the fixed affine base once the frame neighborhood contains the whole boundary. -/
theorem idealFrameMovedCycle_support_isFinite
    (hI : IsLocallyRankOne C (idealModule i))
    {S V : Scheme.{u}} [IsAffine S] [V.IsQuasiAffine]
    (q : C ⟶ S) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
    (hW : (Set.range j)ᶜ ⊆ (W.val : Set C)) (x : C)
    (hx : idealFrameMovedCycle i W e b hb x ≠ 0) :
    IsFinite ((IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ q) := by
  apply Scheme.RelativeCurve.isFinite_closed_support_in_quasiAffine_open q j
  rw [Scheme.IdealSheafData.range_subschemeι, IntegralClosedSubscheme.support_pointClosure]
  intro y hy
  by_contra hn
  exact idealFrameMovedCycle_support_closure i W e b hb hI x hx hy (hW hn)

end AlgebraicGeometry.Scheme
