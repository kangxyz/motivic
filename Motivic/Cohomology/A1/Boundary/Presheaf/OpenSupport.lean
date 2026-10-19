/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Presheaf.OpenZero
public import Motivic.Cohomology.A1.Boundary.Presheaf.PointComparison
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.PointDetection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.InverseImageComposition

/-! # The original presheaf boundary vanishes on its actual open side

Étale localization along the open itself reduces to the identity pair. The
original restriction is invertible there before taking its cokernel. This
uses no global recollement or exactness of a closed direct-image functor.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
section Presheaf
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

variable {U Y : SmoothSite B} (j : U ⟶ Y) [IsOpenImmersion j.left]
  [QuasiCompact j.left]

/-- Every actual full field-valued mark on the open side has zero boundary fiber. -/
theorem fieldPoint_presheafBoundaryAmbient_isZero_of_mem_open
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (p : Spec (.of K))
    (hb : b p ∈ Set.range j.left) :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj (presheafBoundaryAmbient P j)) :=
  fieldPoint_isZero_of_inverseImage_of_mem_range j.left K (presheafBoundaryAmbient P j)
    b p hb (inverseImage_open_presheafBoundaryAmbient_isZero P j)


end Presheaf

section HigherImage
variable (R : CommRingCat.{u}) {U Y : SmoothSite (Spec R)}
  (j : U ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
  {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i]
  (hcomp : Set.range i = (Set.range j.left)ᶜ)
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]

include hcomp in
/-- Actual closed-boundary zero and the proved open-side zero kill the genuine
higher open direct image, detected on every marked point of every test object.
The sole boundary-zero premise concerns the original quotient before sheafification. -/
theorem higherDirectImage_isZero_of_positiveBoundary_zero (n : ℕ)
    (hZ : IsZero ((inverseImage i).obj (presheafBoundaryAmbient
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)) j))) :
    IsZero (((directImage j.left).rightDerived (n + 1)).obj
      ((restrict U AddCommGrpCat).obj F)) := by
  classical
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)
  apply isZero_of_all_marked_residue_fibers
  intro V z
  let K := V.left.residueField z
  let b : Spec K ⟶ Y.left := V.left.fromSpecResidueField z ≫ V.hom
  let p : Spec K := IsLocalRing.closedPoint K
  have hboundary : IsZero ((markedResiduePoint V z).sheafFiber.obj
      (presheafBoundaryAmbient P j)) := by
    by_cases hb : b p ∈ Set.range j.left
    · exact fieldPoint_presheafBoundaryAmbient_isZero_of_mem_open P j K b p hb
    · have hmem : b p ∈ Set.range i := by
        rw [hcomp]
        exact hb
      exact fieldPoint_isZero_of_inverseImage_of_mem_range i K (presheafBoundaryAmbient P j)
        b p hmem hZ
  exact hboundary.of_iso (positiveBoundaryPointHigherImageIso R j
    (markedResiduePoint V z) F n).symm

end HigherImage

end Motivic.FiniteEtaleSite
