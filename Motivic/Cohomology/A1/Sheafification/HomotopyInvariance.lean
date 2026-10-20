/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.WholeCylinderLifting
public import Motivic.Cohomology.A1.Sheafification.CylinderCriterion

/-! # Homotopy invariance of actual Nisnevich sheafification

For `k : Type u`, `[Field k]` and
`P : PresheafWithTransfers.{u + 1} k`,
`nisnevichSheafify_isA1Invariant` derives HI of the actual transfer-preserving
Nisnevich sheafification from `P.IsA1Invariant`.

The argument applies the whole-cylinder lifting producer and the cylinder
criterion to that same sheafification, with its original unit and projection
maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open RelativeProjectiveLine AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic Motivic.PresheafWithTransfers
universe u v w

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- HI of the original presheaf gives HI of its actual Nisnevich sheafification. -/
theorem nisnevichSheafify_isA1Invariant
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ((nisnevichSheafify k).obj P).obj.IsA1Invariant := by
  have hL := modelWholeCylinderLifting_of_isA1Invariant P hP
  exact nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting P hP hL

end Motivic.PresheafWithTransfers
