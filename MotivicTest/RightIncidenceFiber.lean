/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.RightImageFiber
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Arbitrary-field consumers of genuine right incidence geometry

The original finite right image-product map supplies the final Cartesian
base change and all generic fiber lifts. The actual remaining Y list follows
the original ambient and finite-image stalk maps. Nilpotent scheme structures
and arbitrary disconnected smooth-site objects are retained.
-/

@[expose] public section

noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace Motivic.MotivicTest.RightIncidenceFiber

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The original ambient and finite-image scalar routes carry the same Y list. -/
theorem actualRightRemainingList_square (w : F.rightIntermediateSupportProduct G H)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk (F.rightSupportMiddlePair G H w))) :
    (s.map (F.rightImageMiddleStalkMap G H w).hom).map
        ((F.rightIntermediateImageMap G H).stalkMap w).hom =
      (s.map (F.rightAmbientMiddleStalkMap G H w).hom).map
        ((F.rightIntermediateAmbientInclusion G H).stalkMap w).hom :=
  F.rightRemainingList_square G H w s

/-- The final image-incidence square is actually Cartesian over every field. -/
theorem actualRightImageIncidence_isPullback :
    IsPullback (F.tripleToRightImageIncidence G H)
      (F.tripleIncidenceToRightSupportProduct G H)
      (F.rightImageIncidenceInclusion G H) (F.rightIntermediateImageMap G H) :=
  F.tripleToRightImageIncidence_isPullback G H

/-- The final map is finite as the proved base change of the original finite map. -/
theorem actualRightImageIncidence_isFinite : IsFinite (F.tripleToRightImageIncidence G H) :=
  inferInstance

/-- The remaining support kernel retains the actual, potentially nonradical Y ideal. -/
theorem actualRightRemainingIdeal :
    (F.tripleIncidenceToRightSupportProduct G H).ker =
      (pullback.diagonal Y.hom).ker.comap (F.rightSupportMiddlePair G H) :=
  F.rightRemainingDiagonal_kernel G H

/-- The whole source fiber is identified with the whole final-incidence fiber
as point sets only; no splitting of the whole finite algebra is asserted. -/
def actualRightImageIncidenceFiberEquiv (y : F.rightImageIncidence G H) :
    {w : F.tripleIncidence G H // F.tripleToRightImageIncidence G H w = y} ≃
      {x : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y} :=
  F.rightImageIncidenceFiberEquiv G H y

/-- Every branch over a genuine generic final image point has a proved generic
full triple-incidence lift with both original projections retained. -/
theorem actualRightImageIncidenceFiber_genericLift
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (x : F.rightIntermediateSupportProduct G H)
    (hx : F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y) :
    ∃ w : F.tripleIncidence G H, w ∈ genericPoints (F.tripleIncidence G H) ∧
      F.tripleToRightImageIncidence G H w = y ∧
        F.tripleIncidenceToRightSupportProduct G H w = x :=
  F.rightImageIncidenceFiber_lift_generic G H y hy x hx

/-- The genuine smooth Y diagonal constructs a regular list at each actual
right image-incidence point, with no algebraic-closure or dimension premise. -/
theorem actualRightRemainingList_exists (y : F.rightImageIncidence G H) :
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))) s ∧
      (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y)) = Ideal.ofList s :=
  F.exists_rightImageIncidenceRemainingList G H y

end Motivic.MotivicTest.RightIncidenceFiber
