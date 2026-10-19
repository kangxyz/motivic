/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Cartier.DirectImage
public import Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Epi

/-! # Actual Cartier higher-image vanishing from degree-wise homotopy invariance

The original canonical boundary epimorphism is now constructed. Only the
specified positive degree's homotopy invariance remains an induction input;
this is not an assertion of strict A1 invariance in all degrees.
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

include hP

/-- The original positive-degree Cartier boundary is zero; its canonical
boundary epimorphism is discharged by the original-presheaf construction. -/
theorem isZero_cartierBoundary_succ
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero ((EtaleSeparatedFiniteType.inverseImage i).obj (FiniteEtaleSite.presheafBoundaryAmbient
      (_root_.CategoryTheory.Sheaf.LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((SheafWithTransfers.toSheaf k).obj F) (n + 1)) j)) :=
  isZero_cartierBoundary_succ_of_epi k F n hP
    (fun X => FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_epi X _ hP)
    j i hI hcomp

/-- Actual positive higher open direct image vanishes in the specified HI degree.
In degree induction this theorem is used only in the lower-degree window. -/
theorem higherDirectImage_isZero_of_cartier
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero (((EtaleSeparatedFiniteType.directImage j.left).rightDerived (n + 1)).obj
      ((EtaleSeparatedFiniteType.restrict U AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj F))) :=
  higherDirectImage_isZero_of_original_epi k F n hP
    (fun X => FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_epi X _ hP)
    j i hI hcomp

end Motivic.SheafCohomology
