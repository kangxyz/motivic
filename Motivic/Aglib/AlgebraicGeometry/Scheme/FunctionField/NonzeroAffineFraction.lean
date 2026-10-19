/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Nonzero affine representatives of a specified rational function

The prescribed nonempty affine open is unchanged. The numerator and denominator
are actual sections on that open, and their germs are nonzero at every point.
The fraction equality uses the native generic-point germ and actual stalk maps.
This is not a statement that either section is a unit, nor a construction of a
boundary frame or a global polynomial homotopy.


Intended upstream module: `Aglib.AlgebraicGeometry.Scheme.FunctionField.NonzeroAffineFraction`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteCurve.Faces.FiniteDominantFaceCurvePlacement`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyLocalFraction`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A specified nonzero rational function has actual numerator and denominator
sections on the given affine open, nonzero in every original stalk. -/
theorem exists_nonzero_affine_fraction (C : Scheme.{u}) [IsIntegral C]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (h : C.functionField) (hh : h ≠ 0) :
    ∃ a b : Γ(C, U),
      (∀ (x : C) (hx : x ∈ U),
        C.presheaf.germ U x hx a ≠ 0 ∧ C.presheaf.germ U x hx b ≠ 0) ∧
      C.germToFunctionField U a / C.germToFunctionField U b = h := by
  let : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective Γ(C, U) h
  have ha : a ≠ 0 := by
    intro ha
    apply hh
    simpa only [ha, map_zero, zero_div] using hab.symm
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  refine ⟨a, b, ?_, hab⟩
  intro x hx
  constructor
  · intro hz
    exact ha (germ_injective_of_isIntegral C x hx (by simpa using hz))
  · intro hz
    exact hb' (germ_injective_of_isIntegral C x hx (by simpa using hz))

/-- The same representatives compute the specified fraction using the original
local-ring-to-function-field maps, not a replacement fraction field. -/
theorem exists_nonzero_affine_stalk_fraction (C : Scheme.{u}) [IsIntegral C]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (h : C.functionField) (hh : h ≠ 0) :
    ∃ a b : Γ(C, U), ∀ (x : C) (hx : x ∈ U),
      C.presheaf.germ U x hx a ≠ 0 ∧ C.presheaf.germ U x hx b ≠ 0 ∧
      algebraMap (C.presheaf.stalk x) C.functionField (C.presheaf.germ U x hx a) /
        algebraMap (C.presheaf.stalk x) C.functionField (C.presheaf.germ U x hx b) = h := by
  obtain ⟨a, b, hn, hab⟩ := exists_nonzero_affine_fraction C U hU h hh
  refine ⟨a, b, fun x hx => ⟨(hn x hx).1, (hn x hx).2, ?_⟩⟩
  simpa only [Scheme.algebraMap_germ_eq_germToFunctionField] using hab

end AlgebraicGeometry.Scheme
