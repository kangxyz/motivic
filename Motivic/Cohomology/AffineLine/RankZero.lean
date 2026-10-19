/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.AffineLine.HigherVanishing
public import Motivic.Cohomology.Sheaf.H1.AffineLineVanishing

/-! # The actual field rank-zero vanishing endpoint for HI sheaves with transfers -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- All positive ordinary affine-line cohomology vanishes for an HI sheaf with
transfers over a field. This does not assert generic-cylinder model descent. -/
theorem affineLine_H_succ_eq_zero
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj) (n : ℕ)
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (SmoothSite.affineLine (.of k))) :
    e = 0 := by
  cases n with
  | zero => exact h_one_affineLine_eq_zero F hF e
  | succ n => exact affineLine_H_add_two_eq_zero ((SheafWithTransfers.toSheaf k).obj F) n e

end Motivic.SheafCohomology
