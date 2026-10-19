/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.ContractionSheafZero
public import Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Basic
public import Motivic.Cohomology.A1.Boundary.Presheaf.CoefficientIso
public import Motivic.Cohomology.A1.Boundary.Presheaf.SmoothCartierZero

/-! # Original positive-cohomology Cartier boundary zero from explicit boundary Epi

The exact small ordinary sheafification of the unchanged contraction is zero.
An explicit epimorphism premise for the original contraction-to-boundary map
therefore kills each literal zero-section boundary. Actual étale Cartier charts
then kill the genuine closed inverse image for an arbitrary smooth Cartier pair.

The original ordinary cohomology presheaf is reached through
`withTransfersGraphIso`, including its original restrictions, not by a
definitional identification or sheafification of the coefficient first.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology

variable (k : Type u) [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (hE : ∀ X : SmoothSite (Spec (.of k)),
      Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X
        (withTransfers k F (n + 1))))

include hP hE

/-- The explicit original boundary epimorphism sends the exact zero small-site
contraction source onto the actual zero-section boundary. -/
theorem isZero_zeroSectionBoundary_succ_of_epi (X : SmoothSite (Spec (.of k))) :
    IsZero (FiniteEtaleSite.OriginalPresheaf.zeroSectionBoundary X
      (withTransfers k F (n + 1))) := by
  let := hE X
  exact IsZero.of_epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X
    (withTransfers k F (n + 1))) (isZero_smallSheafify_contraction_succ k F n hP X)

/-- For an actual smooth Cartier pair, the genuine closed inverse image of the
original ordinary positive-cohomology quotient is zero. Current-degree HI and
the original boundary Epi remain explicit; no perfect-field premise is needed. -/
theorem isZero_cartierBoundary_succ_of_epi
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero ((EtaleSeparatedFiniteType.inverseImage i).obj
      (FiniteEtaleSite.presheafBoundaryAmbient
        (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) (n + 1)) j)) := by
  have h := FiniteEtaleSite.isZero_presheafBoundary_of_smooth_cartier
    ((PresheafWithTransfers.toPresheaf k).obj (withTransfers k F (n + 1)))
    (isZero_zeroSectionBoundary_succ_of_epi k F n hP hE) j i hI hcomp
  exact h.of_iso ((EtaleSeparatedFiniteType.inverseImage i).mapIso
    (FiniteEtaleSite.presheafBoundaryAmbientCoefficientIso
      (withTransfersGraphIso k F (n + 1)) j)).symm

end Motivic.SheafCohomology
