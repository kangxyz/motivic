/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.AffineLine
import Lean

namespace MotivicTest.SheafCohomologyAffineLineHigherVanishing

/-! # Original ordinary affine-line higher cohomology and transitive trust audit -/

public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.SheafCohomology
universe w u

/-- Literal ordinary Ext endpoint, with no transfer or invariance premise. -/
theorem ordinary_affine_line_higher_zero {k : Type u} [Field k]
    [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (e : H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 2) (SmoothSite.affineLine (.of k))) :
    e = 0 := affineLine_H_add_two_eq_zero F n e

/-- The original rank-zero endpoint includes degree one using the proved pencil theorem. -/
theorem hi_affine_line_positive_zero {k : Type u} [Field k]
    [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj) (n : ℕ)
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (SmoothSite.affineLine (.of k))) :
    e = 0 := affineLine_H_succ_eq_zero F hF n e

open Lean in
run_cmd do
  for name in #[``ordinary_affine_line_higher_zero, ``hi_affine_line_positive_zero,
      ``exists_affineLine_overlap_refinement_zero,
      ``exists_affineLine_positive_zero_square,
      ``exists_all_generic_open_restriction_eq_zero,
      ``ordinary_eq_zero_of_overlap_refinement,
      ``exists_nisnevich_overlap_boundary_lift,
      ``SmoothSite.exists_all_generic_open_section_lift,
      ``Scheme.exists_open_shrinking_of_openImmersion] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Ordinary H^(n+2) and HI rank-zero H^(n+1): standard foundations only."

end

end MotivicTest.SheafCohomologyAffineLineHigherVanishing
