/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduced ideal sheaves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The ideal sheaf of an actual reduced closed subscheme is radical. -/
theorem radical_eq_of_isReduced_subscheme (I : X.IdealSheafData) [IsReduced I.subscheme] :
    I.radical = I := by
  ext U : 2
  change (I.ideal U).radical = I.ideal U
  apply Ideal.radical_eq_iff.mpr
  rw [← I.ker_subschemeι_app U]
  exact (RingHom.ker_isRadical_iff_reduced_of_surjective
    (I.subschemeι_app_surjective U)).mpr inferInstance

/-- Reduced closed subschemes with the same closed support have the same ideal sheaf. -/
theorem idealSheaf_eq_of_support_eq (I J : X.IdealSheafData)
    [IsReduced I.subscheme] [IsReduced J.subscheme] (h : I.support = J.support) : I = J := by
  rw [← radical_eq_of_isReduced_subscheme I, ← radical_eq_of_isReduced_subscheme J,
    ← Scheme.IdealSheafData.vanishingIdeal_support,
    ← Scheme.IdealSheafData.vanishingIdeal_support, h]

end AlgebraicGeometry.Scheme.IdealSheafData
