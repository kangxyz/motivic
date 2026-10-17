/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.LengthEuler
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Length Euler characteristics of complexes concentrated in one degree

The computation applies to mathlib's actual single complexes over any ring.
In particular, it does not require the one nonzero module to be free.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe u v w

namespace Motivic.LengthEuler

variable {R : Type u} [Ring R] {ι : Type w} [DecidableEq ι]
variable (c : ComplexShape ι) (j : ι) (M : ModuleCat.{v} R)

/-- A single complex on a finite-length module has finite-length homology support. -/
theorem finiteHomology_single (hM : Module.length R M ≠ ⊤) :
    FiniteHomology ((single (ModuleCat R) c j).obj M) := by
  refine FiniteLengthSupport.of_isZero_outside _ {j} ?_ ?_
  · intro i hi
    have hi' : i = j := Finset.mem_singleton.mp hi
    subst i
    rw [(singleObjHomologySelfIso c j M).toLinearEquiv.length_eq]
    exact hM
  · intro i hi
    exact isZero_single_obj_homology c j M i (by simpa using hi)

/-- The actual single-complex homology Euler sum is the signed module length. -/
theorem homologyEuler_single (sign : ι → ℤ) (hM : Module.length R M ≠ ⊤) :
    homologyEuler ((single (ModuleCat R) c j).obj M) sign (finiteHomology_single c j M hM) =
      sign j * integerLength M hM := by
  change (∑ᶠ i, sign i * integerLength _ _) = _
  rw [finsum_eq_single _ j]
  · rw [integerLength_eq_of_equiv (singleObjHomologySelfIso c j M).toLinearEquiv]
  · intro i hi
    have : Subsingleton (((single (ModuleCat R) c j).obj M).homology i) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_homology c j M i hi)
    simp [integerLength]

end Motivic.LengthEuler
