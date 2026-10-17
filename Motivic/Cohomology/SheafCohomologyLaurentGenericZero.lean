/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeLaurentNeighborhoodZero
public import Motivic.Transfers.SheafCohomologyWithTransfers
/-! # Positive ordinary torus classes vanish after shrinking an actual smooth integral model -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial Opposite
open AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace Motivic.SheafCohomology
open RelativePolynomialOpenSpans
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Under the explicit current-degree HI induction premise, every original positive
ordinary class on the whole relative torus dies after one base localization. -/
theorem exists_laurent_base_shrink_succ_eq_zero
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) (n + 1) (openSite (k := k) (X : R[X]))) :
    ∃ r : R, r ≠ 0 ∧
      (presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) (n + 1)).map
          (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op e = 0 := by
  let T := openSite (k := k) (X : R[X])
  let : IsIntegral T.left := IsIntegral.of_isIso (laurentSchemeIso (R := R)).hom
  obtain ⟨W, hW, hz⟩ := exists_generic_open_restriction_eq_zero
    ((SheafWithTransfers.toSheaf k).obj F) n T e
  have hs : (withTransfers k F (n + 1)).transfer ((Cor.graphFunctor k).map
      (SmoothSite.openInclusion T W)) e = 0 := by
    rw [withTransfers_graph]
    exact hz
  obtain ⟨r, hr, he⟩ := exists_base_shrink_of_neighborhood_zero
    (withTransfers k F (n + 1)) hP W ⟨genericPoint T.left, hW⟩ e hs
  refine ⟨r, hr, ?_⟩
  rw [withTransfers_graph] at he
  exact he

end Motivic.SheafCohomology
