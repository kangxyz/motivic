/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyCartierBoundaryZero
public import Motivic.Cohomology.A1.PresheafBoundaryOpenSupport

/-!
# Original positive open direct image for a smooth Cartier complement

The boundary-zero theorem and the actual point-fiber comparison imply zero
of the genuine positive right-derived open direct image. The current-degree
ordinary cohomology presheaf must be A1-invariant, and its original
contraction-to-boundary map must be epimorphic for every smooth object.
These remain explicit inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace Motivic.SheafCohomology

variable (k : Type u) [Field k] [Infinite k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
  (hP : (SheafCohomology.withTransfers k F (n + 1)).IsA1Invariant)
  (hE : ∀ X : SmoothSite (Spec (.of k)),
    Epi (FiniteEtaleSite.OriginalPresheaf.contractionToBoundary X
      (SheafCohomology.withTransfers k F (n + 1))))

include hP hE

/-- Actual positive open direct image vanishes under the retained original Epi input. -/
theorem higherDirectImage_isZero_of_original_epi
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero (((FiniteEtaleSite.directImage j.left).rightDerived (n + 1)).obj
      ((FiniteEtaleSite.restrict U AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj F))) :=
  FiniteEtaleSite.higherDirectImage_isZero_of_positiveBoundary_zero (.of k) j i hcomp
    ((SheafWithTransfers.toSheaf k).obj F) n
    (SheafCohomology.isZero_cartierBoundary_succ_of_epi k F n hP hE j i hI hcomp)

end Motivic.SheafCohomology

end
