/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Polynomial.BoundaryOneRationalFunctions.Basic

/-!
# Admissible boundary-one rational functions
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

universe u

namespace Polynomial.BoundaryOneRationalFunctions

variable (R : Type u) [CommRing R]

/-- Actual monic rational fractions regular and invertible at zero, with
arbitrary order at infinity and arbitrary invertible value at zero. -/
def admissibleGroup : Subgroup (Ring R)ˣ where
  carrier := {f | ∃ p q : denominators R, f = fraction p q}
  one_mem' := ⟨1, 1, (fraction_self 1).symm⟩
  mul_mem' := by
    rintro f g ⟨p, q, rfl⟩ ⟨r, s, rfl⟩
    exact ⟨p * r, q * s, fraction_mul p q r s⟩
  inv_mem' := by
    rintro f ⟨p, q, rfl⟩
    exact ⟨q, p, fraction_inv p q⟩

variable {R}

/-- A literal admissible numerator-denominator pair. -/
def admissibleFraction (p q : denominators R) : admissibleGroup R :=
  ⟨fraction p q, p, q, rfl⟩

@[simp] theorem admissibleFraction_self (p : denominators R) :
    admissibleFraction p p = 1 := Subtype.ext (fraction_self p)

theorem admissibleFraction_mul (p q r s : denominators R) :
    admissibleFraction p q * admissibleFraction r s =
      admissibleFraction (p * r) (q * s) := Subtype.ext (fraction_mul p q r s)

/-- The original boundary-one subgroup sits inside the larger actual fraction group. -/
def boundaryInclusion : group R →* admissibleGroup R where
  toFun f := ⟨f.val, by obtain ⟨p, q, _, _, h⟩ := f.property; exact ⟨p, q, h⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Polynomial.BoundaryOneRationalFunctions
