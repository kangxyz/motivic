/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.FinitePresheafContractionBoundaryEpi
public import Motivic.Cohomology.A1.FiniteCoefficientLocalZero
public import Motivic.Cohomology.A1.StrictInvarianceCoefficientInputs

/-! # Strict invariance over finite fields

The original finite-field local-zero and canonical-boundary producers discharge
both geometric inputs of the degree-induction assembly. The coefficient universe
and ordinary cohomological HasExt assumption are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.SheafWithTransfers

variable {k : Type u} [Field k] [Finite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every HI Nisnevich sheaf with transfers over a finite field is strictly
A1-invariant for the original ordinary cohomological projection maps. -/
theorem isStrictA1Invariant_of_finite
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    F.IsStrictA1Invariant :=
  isStrictA1Invariant_of_coefficient_inputs
    (PresheafWithTransfers.integralAffineLocalZero_of_finite k)
    FiniteEtaleSite.OriginalPresheaf.canonicalBoundaryEpi_of_finite F hF

end Motivic.SheafWithTransfers
