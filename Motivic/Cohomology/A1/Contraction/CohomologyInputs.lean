/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Contraction.Inputs
public import Motivic.Cohomology.Sheaf.TorusModelGerm
public import Motivic.Transfers.Presheaf.ContractionInvariance

/-! # Conditional vanishing of the original cohomology boundary

Original local-zero detection and canonical boundary Epi remain explicit inputs.
The source is literal small-site sheafification, with unchanged ordinary cohomology.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The exact small source of the original boundary is zero in a specified
positive HI degree, from original local-zero detection rather than a sheafification exchange. -/
theorem isZero_smallSheafify_contraction_succ_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1}).obj
      ((EtaleSeparatedFiniteType.toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
        (PresheafWithTransfers.contraction (withTransfers k F (n + 1))))) := by
  apply FiniteEtaleSite.isZero_sheafify_of_genericModelGerm_eq_zero_of_integralAffineLocalZero
    hD _ (PresheafWithTransfers.contraction_isA1Invariant _ hP)
  intro T _ _ s
  exact contraction_genericModelGerm_succ_eq_zero.{0, u} k F n hP T s

/-- Original local zero and original canonical Epi kill the actual zero-section
boundary. In strict induction the displayed HI degree must be below the target. -/
theorem isZero_zeroSectionBoundary_succ_of_coefficient_inputs
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (hE : FiniteEtaleSite.OriginalPresheaf.CanonicalBoundaryEpi k)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    IsZero (FiniteEtaleSite.OriginalPresheaf.zeroSectionBoundary X
      (withTransfers k F (n + 1))) := by
  let := hE X (withTransfers k F (n + 1)) hP
  exact IsZero.of_epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X
    (withTransfers k F (n + 1)))
    (isZero_smallSheafify_contraction_succ_of_integralAffineLocalZero hD F n hP X)

end Motivic.SheafCohomology
