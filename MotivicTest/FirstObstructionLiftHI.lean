/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.FirstObstructionLiftHI
public import Motivic.AlgebraicGeometry.SmoothSiteInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Lean.Util.CollectAxioms

/-! # Original HI and lower-degree HI supply the actual first-obstruction lift -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace MotivicTest.FirstObstructionLiftHI
open Motivic Motivic.FiniteEtaleSite
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)
local instance : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _
local instance : HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Only persistent germs of the actual first obstruction remain as the inner-rank input.
Both the degree-zero coefficient iso and the lower higher-image window are proved from HI. -/
theorem actual_original_lift
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (V : FiniteEtaleSite X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (α : SheafCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N
        ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj
          ((baseChange (SmoothSite.a1Projection (.of k) X).left).obj V)))
    (hα : ∀ y : V.left, g y ⤳ z →
      markedSectionGerm
        (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived N).obj
          ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
            ((SheafWithTransfers.toSheaf k).obj F))).obj V y
        (originalFirstObstruction (SmoothSite.a1Projection (.of k) X)
          ((SheafWithTransfers.toSheaf k).obj F) N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      (SheafCohomology.presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) N).map
          ((restrictionProjection (SmoothSite.a1Projection (.of k) X)).app
            (testOpenObject V (g ⁻¹ᵁ O))).op β =
      (SheafCohomology.presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) N).map
          ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).map
            ((baseChange (SmoothSite.a1Projection (.of k) X).left).map
              (testOpenInclusion V (g ⁻¹ᵁ O)))).op α :=
  SheafWithTransfers.a1_exists_open_originalRestriction_lift X F hF N hN hLow V g z α hα

open Lean in
run_cmd do
  for name in #[``actual_original_lift,
      ``Motivic.FiniteEtaleSite.originalFirstObstruction_eq_zero_iff,
      ``Motivic.FiniteEtaleSite.originalFirstObstruction_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original HI first-obstruction lift: standard axioms only."

end MotivicTest.FirstObstructionLiftHI
