/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.FiniteField.LerayHI
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! Direct original transfer-HI projection consumers with no extra coefficient-iso premise. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FiniteLerayHI
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Motivic _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
local instance : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Original HI alone supplies the actual coefficient isomorphism. -/
theorem actual_coefficient_iso (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    IsIso (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F)
      (SmoothSite.a1Projection (.of k) X)) := F.a1_coefficient_isIso X hF

/-- Only the actual higher direct-image vanishing remains as a finite-window input. -/
theorem actual_projection_bijective (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N →
      IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived q).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
          ((SheafWithTransfers.toSheaf k).obj F)))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) N) X) :=
  F.a1_projection_bijective_of_rightDerived_window X hF N hR

open Lean in
run_cmd do
  for name in #[``actual_coefficient_iso, ``actual_projection_bijective,
      ``Motivic.SheafWithTransfers.a1_projection_injective_of_rightDerived_window,
      ``a1BaseChangeIso_hom_projection,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.a1RestrictionCoefficient_app] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "HI coefficient iso and original finite-window projection: standard axioms only."

end MotivicTest.FiniteLerayHI
