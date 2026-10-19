/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.Sheaf.TorusModelGerm
public import Lean
/-! # Direct original OpenNhds-colimit consumers, with explicit current-degree HI -/
public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite (nisnevichTopology opensFunctor)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Motivic
open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Motivic.SheafCohomology
universe w u
namespace MotivicTest.SheafCohomologyTorusModelGerm
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable (k : Type u) [Field k]
    [HasExt.{max w (u + 1)}
      (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The endpoint is literally the colimit over original model generic neighborhoods. -/
theorem actual_torus_colimit_zero (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (s : (colimit ((OpenNhds.inclusion (genericPoint X.left)).op ⋙
      (opensFunctor X).op ⋙
        (toPresheaf k).obj (torusSections (withTransfers k F (n + 1)))) :
          AddCommGrpCat.{max w (u + 1)})) : s = 0 :=
  torus_genericModelGerm_succ_eq_zero k F n hP X s

/-- The original contraction quotient, before any unsupported sheafification exchange. -/
theorem actual_contraction_colimit_zero (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (s : (colimit ((OpenNhds.inclusion (genericPoint X.left)).op ⋙
      (opensFunctor X).op ⋙
        (toPresheaf k).obj (contraction (withTransfers k F (n + 1)))) :
          AddCommGrpCat.{max w (u + 1)})) : s = 0 :=
  contraction_genericModelGerm_succ_eq_zero k F n hP X s

open Lean in
run_cmd do
  for name in #[``actual_torus_colimit_zero, ``actual_contraction_colimit_zero,
      ``torus_affineLocalizationZero, ``contraction_affineLocalizationZero,
      ``PresheafWithTransfers.genericModelGerm_eq_zero,
      ``puncturedProductIso_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original torus/contraction model colimits: standard foundations only."

end MotivicTest.SheafCohomologyTorusModelGerm
