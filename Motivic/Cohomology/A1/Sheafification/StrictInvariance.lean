/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.CylinderCriterion
public import Motivic.Cohomology.A1.StrictInvariance.PerfectField

/-! # Conditional strict invariance of the actual Nisnevich sheafification

Whole-cylinder lifting and homotopy invariance of the original presheaf give
strict invariance over a perfect field. Every degree retains the literal ordinary
cohomology projection, coefficient universe and ordinary `HasExt` hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

universe u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Whole-cylinder lifting gives strict invariance for every original ordinary
cohomology projection of the actual Nisnevich sheafification. -/
theorem nisnevichSheafify_isStrictA1Invariant_of_modelWholeCylinderLifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hL : ModelWholeCylinderLifting P) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    IsIso ((_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P)) n).map
          (SmoothSite.a1Projection (.of k) X).op) :=
  SheafWithTransfers.isStrictA1Invariant_of_perfect ((nisnevichSheafify k).obj P)
    (nisnevichSheafify_isA1Invariant_of_modelWholeCylinderLifting P hP hL) n X

end Motivic.PresheafWithTransfers
