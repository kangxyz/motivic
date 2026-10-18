/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyTorusModelGerm
public import Motivic.Cohomology.A1.FiniteEtaleGenericModelDetection
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance

/-! # The original positive-cohomology contraction has zero sheafification

Over an infinite field, the already proved generic-model contraction vanishing
and genuine generic detection give the zero Nisnevich sheafification. The sole
inductive mathematical premise is ordinary A1 invariance in the current positive
degree. This is not strict A1 invariance or an exchange of contraction with
sheafification of the cohomology presheaf.

The original ordinary `HasExt` is used in universe `u + 1`, the coefficient
universe supported by the existing canonical transfer sheafification functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SheafCohomology

variable (k : Type u) [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Sheafify the original cokernel contraction of the original ordinary positive
cohomology presheaf. Current-degree HI remains an explicit induction hypothesis. -/
theorem isZero_nisnevichSheafify_contraction_succ
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) :
    IsZero ((PresheafWithTransfers.nisnevichSheafify k).obj
      (PresheafWithTransfers.contraction (withTransfers k F (n + 1)))) := by
  apply PresheafWithTransfers.isZero_nisnevichSheafify_of_genericModelGerm_eq_zero
    _ (PresheafWithTransfers.contraction_isA1Invariant _ hP)
  intro X _ _ s
  exact contraction_genericModelGerm_succ_eq_zero.{0, u} k F n hP X s

/-- The canonical unit out of the unchanged contraction presheaf is zero. -/
theorem toNisnevichSheafify_contraction_succ_eq_zero
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) :
    PresheafWithTransfers.toNisnevichSheafify k
      (PresheafWithTransfers.contraction (withTransfers k F (n + 1))) = 0 := by
  exact ((SheafWithTransfers.forget k).map_isZero
    (isZero_nisnevichSheafify_contraction_succ k F n hP)).eq_of_tgt _ _

/-- The exact small-site source of the original presheaf contraction boundary
is zero, proved by literal small-site covers of the unchanged contraction. -/
theorem isZero_smallSheafify_contraction_succ
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (FiniteEtaleSite.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1}).obj
      ((FiniteEtaleSite.toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
        (PresheafWithTransfers.contraction (withTransfers k F (n + 1))))) := by
  apply FiniteEtaleSite.isZero_sheafify_of_genericModelGerm_eq_zero
    _ (PresheafWithTransfers.contraction_isA1Invariant _ hP)
  intro T _ _ s
  exact contraction_genericModelGerm_succ_eq_zero.{0, u} k F n hP T s

end Motivic.SheafCohomology
