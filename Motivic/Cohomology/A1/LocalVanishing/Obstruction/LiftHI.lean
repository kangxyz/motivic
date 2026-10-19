/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.FirstObstructionNaturality
public import Motivic.Cohomology.A1.LocalVanishing.FiniteField.LerayHI
public import Motivic.Cohomology.A1.HigherImages.ProjectionHI

/-! # Original HI and lower-degree HI supply the actual first-obstruction lift -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType _root_.Motivic.FiniteEtaleSite
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (Scheme.EtaleSeparatedFiniteType.nisnevichTopology X.left) AddCommGrpCat.{u
      + 1})]
  [HasExt.{u + 1} (Sheaf (Scheme.EtaleSeparatedFiniteType.nisnevichTopology (SmoothSite.a1Cylinder
      (.of k) X).left)
    AddCommGrpCat.{u + 1})]

/-- Lower-degree ordinary HI gives the actual lower positive right-image window. -/
theorem a1_lower_rightDerived_isZero (N : ℕ)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant) :
    ∀ q : ℕ, 0 < q → q < N →
      IsZero (((Scheme.EtaleSeparatedFiniteType.directImage (SmoothSite.a1Projection (.of k)
          X).left).rightDerived q).obj
        ((Scheme.EtaleSeparatedFiniteType.restrict (SmoothSite.a1Cylinder (.of k) X)
            AddCommGrpCat.{u + 1}).obj
          ((toSheaf k).obj F))) := by
  intro q hq hqN
  cases q with
  | zero => omega
  | succ n => exact projectionHigherImage_isZero_of_cohomology_HI k X F n (hLow _ hq hqN)

/-- Only persistent germs of the actual first obstruction remain as the inner-rank input.
Both the degree-zero coefficient iso and the lower higher-image window are proved from HI. -/
theorem a1_exists_open_originalRestriction_lift
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (V : EtaleSeparatedFiniteType X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (α : LargeCohomology.H.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) N
        ((Scheme.EtaleSeparatedFiniteType.toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj
          ((Scheme.EtaleSeparatedFiniteType.baseChange (SmoothSite.a1Projection (.of k) X).left).obj
              V)))
    (hα : ∀ y : V.left, g y ⤳ z →
      Scheme.EtaleSeparatedFiniteType.markedSectionGerm
        (((Scheme.EtaleSeparatedFiniteType.directImage (SmoothSite.a1Projection (.of k)
            X).left).rightDerived N).obj
          ((Scheme.EtaleSeparatedFiniteType.restrict (SmoothSite.a1Cylinder (.of k) X)
              AddCommGrpCat.{u + 1}).obj
            ((toSheaf k).obj F))).obj V y
        (Scheme.EtaleSeparatedFiniteType.originalFirstObstruction (SmoothSite.a1Projection (.of k)
            X)
          ((toSheaf k).obj F) N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      (LargeCohomology.presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf k).obj F) N).map
          ((Scheme.EtaleSeparatedFiniteType.restrictionProjection (SmoothSite.a1Projection (.of k)
              X)).app
            (Scheme.EtaleSeparatedFiniteType.testOpenObject V (g ⁻¹ᵁ O))).op β =
      (LargeCohomology.presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf k).obj F) N).map
          ((Scheme.EtaleSeparatedFiniteType.toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).map
            ((Scheme.EtaleSeparatedFiniteType.baseChange (SmoothSite.a1Projection (.of k)
                X).left).map
              (Scheme.EtaleSeparatedFiniteType.testOpenInclusion V (g ⁻¹ᵁ O)))).op α := by
  let := a1_coefficient_isIso X F hF
  exact exists_open_originalRestriction_lift_of_persistent_obstruction_germs
    (SmoothSite.a1Projection (.of k) X) ((toSheaf k).obj F) N hN V g z
      (a1_lower_rightDerived_isZero X F N hLow) α hα

end Motivic.SheafWithTransfers
