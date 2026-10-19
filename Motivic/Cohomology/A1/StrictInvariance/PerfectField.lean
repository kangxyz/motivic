/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.StrictInvariance.InfiniteField
public import Motivic.Cohomology.A1.StrictInvariance.FiniteField

/-! # Strict invariance over every perfect field

The finite and infinite perfect-field theorems combine without a cardinality
assumption. The original ordinary cohomology projections, coefficient universe,
and ordinary HasExt hypothesis are retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every HI Nisnevich sheaf with transfers over a perfect field is strictly
A1-invariant for the original ordinary cohomological projections. -/
theorem isStrictA1Invariant_of_perfect
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant := by
  cases finite_or_infinite k
  · exact isStrictA1Invariant_of_finite F hF
  · exact isStrictA1Invariant_of_isA1Invariant F hF

/-- Over any perfect field, strict ordinary cohomological invariance is
 equivalent to coefficient-level homotopy invariance. -/
theorem isStrictA1Invariant_iff_isA1Invariant_of_perfect
    (F : SheafWithTransfers.{u + 1} k) :
    F.IsStrictA1Invariant ↔ F.obj.IsA1Invariant :=
  ⟨fun hF => hF.isA1Invariant, isStrictA1Invariant_of_perfect F⟩

end Motivic.SheafWithTransfers
