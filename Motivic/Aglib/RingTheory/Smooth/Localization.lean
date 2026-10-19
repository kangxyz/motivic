/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Basic

/-! # Extracted ordinary primitive with the original parameters and maps -/

@[expose] public noncomputable section
universe v u
namespace Algebra.Smooth
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- Localization in a base element is a genuine smooth k-algebra. -/
theorem away_smooth (r : R) : Algebra.Smooth k (Localization.Away r) := by
  let : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  exact Algebra.Smooth.comp k R (Localization.Away r)

end Algebra.Smooth
