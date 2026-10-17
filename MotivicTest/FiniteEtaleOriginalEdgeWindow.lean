/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalEdgeWindow
public import Motivic.Cohomology.A1.Basic
public import Motivic.AlgebraicGeometry.SmoothSiteInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Direct consumer of the original affine-line projection, with a transitive axiom audit. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace MotivicTest.FiniteEtaleOriginalEdgeWindow
open Motivic Motivic.FiniteEtaleSite
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
local instance : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder R X).left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The conclusion is literally the original affine-line projection pullback.
Only the explicit degree-zero coefficient iso and finite derived window are inputs. -/
theorem actual_a1_projection_bijective
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    [IsIso (restrictionToDirectImage F (SmoothSite.a1Projection R X))] (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N →
      IsZero (((directImage (SmoothSite.a1Projection R X).left).rightDerived q).obj
        ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat.{u + 1}).obj F))) :
    Function.Bijective (A1.projectionPullback R
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F N) X) :=
  originalRestriction_bijective_of_rightDerived_window (SmoothSite.a1Projection R X) F N hR

/-- The original degree-one projection is injective under the degree-zero coefficient iso alone. -/
theorem actual_a1_projection_one_injective
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    [IsIso (restrictionToDirectImage F (SmoothSite.a1Projection R X))] :
    Function.Injective (A1.projectionPullback R
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F 1) X) :=
  originalRestriction_injective_of_rightDerived_window (SmoothSite.a1Projection R X) F 1
    (fun q hq hqN => by omega)

open Lean in
run_cmd do
  for name in #[``actual_a1_projection_bijective, ``actual_a1_projection_one_injective,
      ``Motivic.FiniteEtaleSite.originalRestriction_bijective_of_rightDerived_window,
      ``Motivic.FiniteEtaleSite.originalRestriction_injective_of_rightDerived_window] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original affine-line projection finite-window consumer: standard axioms only."

end MotivicTest.FiniteEtaleOriginalEdgeWindow
