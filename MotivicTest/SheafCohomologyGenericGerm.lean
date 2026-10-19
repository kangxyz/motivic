/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.GenericGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean

/-! # Actual generic filtered germs over an arbitrary field -/
public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite (nisnevichTopology)
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open Motivic _root_.CategoryTheory.Sheaf.LargeCohomology _root_.Motivic.SheafCohomology
universe u
namespace MotivicTest.SheafCohomologyGenericGerm
variable (k : Type u) [Field k]

local instance ordinaryHasExt :
    HasExt.{u + 1} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

example (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    IsFiltered (TopologicalSpace.OpenNhds (genericPoint X.left))ᵒᵖ := inferInstance

/-- No perfectness, homotopy invariance, continuity or vanishing premise is supplied. -/
theorem actual_generic_germ_eq_zero
    (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (e : genericGerm.{u, u} F (n + 1) X) : e = 0 :=
  genericGerm_succ_eq_zero F n X e

open Lean in
run_cmd do
  for name in #[``actual_generic_germ_eq_zero,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.sheaf_isGrothendieckAbelian,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_generic_open_mem_covering_sieve,
      ``_root_.CategoryTheory.Sheaf.LargeCohomology.exists_generic_open_restriction_eq_zero,
      ``exists_smaller_generic_open_restriction_eq_zero, ``genericGerm_succ_eq_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Generic-open restrictions and filtered-colimit vanishing: standard foundations only."

end MotivicTest.SheafCohomologyGenericGerm
