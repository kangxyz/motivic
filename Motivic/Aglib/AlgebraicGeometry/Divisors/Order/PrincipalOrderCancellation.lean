/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Native local orders and cancellation against a rational frame

The actual order of a nonzero local equation is its original stalk quotient
length. Multiplication by the rational ratio of a unit frame cancels that
order, even where the denominator vanishes. No unit condition is imposed on
the ratio. These local identities do not assert global representability.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The original order of a nonzero local equation is the length of its actual
principal quotient in the original ambient stalk. -/
theorem ord_germ_eq_quotient_length (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) (hr : r ≠ 0) {x : X} (hxU : x ∈ U) (hx : coheight x = 1) :
    X.ord (X.germToFunctionField U r) x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU r})).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : X.presheaf.germ U x hxU r ≠ 0 :=
    (map_ne_zero_iff (X.presheaf.germ U x hxU).hom
      (germ_injective_of_isIntegral X x hxU)).mpr hr
  have hf : X.germToFunctionField U r ≠ 0 :=
    (map_ne_zero_iff (X.germToFunctionField U).hom
      (X.germToFunctionField_injective U)).mpr hr
  apply (X.ord_eq_iff hx hf).mpr
  change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField U r) = _
  rw [← X.algebraMap_germ_eq_germToFunctionField hxU r, Ring.ordFrac_eq_ord _ hg]
  apply Ring.ordMonoidWithZeroHom_eq_coe (X.presheaf.stalk x)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  exact (ENat.natCast_toNat (Ring.ord_ne_top
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg))).symm

/-- The native orders cancel the denominator without assuming the ratio is a unit. -/
theorem ord_add_ord_ratio (s t : X.functionField) (hs : s ≠ 0) (ht : t ≠ 0) (x : X) :
    X.ord s x + X.ord (t / s) x = X.ord t x := by
  rw [← X.ord_mul hs (div_ne_zero ht hs), mul_div_cancel₀ t hs]

/-- On the specified frame neighborhood, a unit numerator cancels the original
denominator's order, including at zeros of that denominator. -/
theorem ord_add_ord_unit_ratio_eq_zero (U : X.Opens) [Nonempty U]
    (r b : Γ(X, U)) (hr : r ≠ 0) (hb : IsUnit b) {x : X} (hx : x ∈ U) :
    X.ord (X.germToFunctionField U r) x +
      X.ord (X.germToFunctionField U b / X.germToFunctionField U r) x = 0 := by
  rw [X.ord_add_ord_ratio _ _
    ((map_ne_zero_iff (X.germToFunctionField U).hom
      (X.germToFunctionField_injective U)).mpr hr)
    ((hb.map (X.germToFunctionField U).hom).ne_zero), X.ord_of_isUnit hb hx]

/-- The actual principal quotient length, not an assumed cycle coefficient,
is canceled by the original rational frame ratio. -/
theorem quotient_length_add_ord_unit_ratio_eq_zero (U : X.Opens) [Nonempty U]
    (r b : Γ(X, U)) (hr : r ≠ 0) (hb : IsUnit b) {x : X}
    (hxU : x ∈ U) (hx : coheight x = 1) :
    ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU r})).toNat : ℤ) +
      X.ord (X.germToFunctionField U b / X.germToFunctionField U r) x = 0 := by
  rw [← X.ord_germ_eq_quotient_length U r hr hxU hx]
  exact X.ord_add_ord_unit_ratio_eq_zero U r b hr hb hxU

end AlgebraicGeometry.Scheme
