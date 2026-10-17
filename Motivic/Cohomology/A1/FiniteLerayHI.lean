/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleA1Coefficient
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalEdgeWindow

/-! # The original HI projection: finite Leray consumers without a coefficient-iso premise -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.SheafWithTransfers
open FiniteEtaleSite
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)

/-- Original transfer HI proves the actual degree-zero direct-image coefficient isomorphism. -/
theorem a1_coefficient_isIso (hF : F.obj.IsA1Invariant) :
    IsIso (restrictionToDirectImage ((toSheaf k).obj F)
      (SmoothSite.a1Projection (.of k) X)) :=
  a1RestrictionCoefficient_isIso (.of k) X ((toSheaf k).obj F) hF

variable [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) X).left)
    AddCommGrpCat.{u + 1})]

/-- Original HI gives projection bijectivity under the actual finite higher-image window. -/
theorem a1_projection_bijective_of_rightDerived_window (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N →
      IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived q).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
          ((toSheaf k).obj F)))) :
    Function.Bijective (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) N) X) := by
  let := a1_coefficient_isIso X F hF
  exact originalRestriction_bijective_of_rightDerived_window
    (SmoothSite.a1Projection (.of k) X) ((toSheaf k).obj F) N hR

/-- The endpoint-free higher-image window gives injectivity of the same original projection. -/
theorem a1_projection_injective_of_rightDerived_window (hF : F.obj.IsA1Invariant) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q < N →
      IsZero (((directImage (SmoothSite.a1Projection (.of k) X).left).rightDerived q).obj
        ((restrict (SmoothSite.a1Cylinder (.of k) X) AddCommGrpCat.{u + 1}).obj
          ((toSheaf k).obj F)))) :
    Function.Injective (A1.projectionPullback (.of k)
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) N) X) := by
  let := a1_coefficient_isIso X F hF
  exact originalRestriction_injective_of_rightDerived_window
    (SmoothSite.a1Projection (.of k) X) ((toSheaf k).obj F) N hR

end Motivic.SheafWithTransfers
