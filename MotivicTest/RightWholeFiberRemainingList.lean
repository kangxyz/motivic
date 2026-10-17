/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightWholeFiberRemainingList
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual right whole-fiber remaining-Y list consumers

Over every field, a single original Y-diagonal list is chosen at the image
of a genuine triple point. The actual image-product stalk action carries this
same list to every original source point, through the ambient route as well.
The final-incidence map is the proved finite Cartesian base change.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace Motivic.MotivicTest.RightWholeFiberRemainingList

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- Smoothness supplies one genuine remaining-Y list, simultaneously valid
at every point of the complete original right finite fiber. -/
theorem actualSmoothRightWholeFiberRemainingList (w : F.tripleIncidence G H) :
    let y := F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w)
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H y)),
      RingTheory.Sequence.IsRegular
        ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H y)) s ∧
      (pullback.diagonal Y.hom).ker.stalk (F.rightImageMiddlePair G H y) = Ideal.ofList s ∧
      ∀ x : {x : F.rightIntermediateSupportProduct G H // F.rightIntermediateImageMap G H x = y},
        (pullback.diagonal Y.hom).ker.stalk (F.rightSupportMiddlePair G H x.1) =
            Ideal.ofList (F.rightFiberMiddleList G H y s x) ∧
          (F.rightTargetRemainingList G H y s).map
              (Graph.alignedStalkMap (F.rightIntermediateImageMap G H) x.1 y x.2.symm).hom =
            ((F.rightFiberMiddleList G H y s x).map
              (F.rightAmbientMiddleStalkMap G H x.1).hom).map
                ((F.rightIntermediateAmbientInclusion G H).stalkMap x.1).hom := by
  dsimp only
  obtain ⟨s, hs, hker⟩ := F.exists_rightTripleImageRemainingList G H w
  exact ⟨s, hs, hker, fun x => ⟨F.rightFiberMiddleList_kernel G H _ s hker x,
    F.rightFiberRemainingList_square G H _ s x⟩⟩

/-- Every actual right final-incidence image also supplies the same original
Y list to its whole ambient finite fiber, without a range witness input. -/
theorem actualSmoothRightImageWholeFiberList (y : F.rightImageIncidence G H) :
    ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (F.rightImageIncidenceInclusion G H y))) s ∧
      ∀ x : {x : F.rightIntermediateSupportProduct G H //
          F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y},
        (pullback.diagonal Y.hom).ker.stalk (F.rightSupportMiddlePair G H x.1) =
            Ideal.ofList (F.rightFiberMiddleList G H (F.rightImageIncidenceInclusion G H y) s x) ∧
          (F.rightTargetRemainingList G H (F.rightImageIncidenceInclusion G H y) s).map
              (Graph.alignedStalkMap (F.rightIntermediateImageMap G H) x.1
                (F.rightImageIncidenceInclusion G H y) x.2.symm).hom =
            (F.rightFiberMiddleList G H (F.rightImageIncidenceInclusion G H y) s x).map
              ((F.rightSupportMiddlePair G H).stalkMap x.1).hom := by
  obtain ⟨s, hs, hker⟩ := F.exists_rightImageIncidenceRemainingList G H y
  exact ⟨s, hs, fun x => ⟨F.rightFiberMiddleList_kernel G H _ s hker x,
    F.rightFiberRemainingList_map G H _ s x⟩⟩

/-- The actual final-incidence map is the genuine Cartesian base change of
the original right image-product finite map. -/
theorem actualSmoothRightFinalMap_isPullback :
    IsPullback (F.tripleToRightImageIncidence G H)
      (F.tripleIncidenceToRightSupportProduct G H)
      (F.rightImageIncidenceInclusion G H) (F.rightIntermediateImageMap G H) :=
  F.tripleToRightImageIncidence_isPullback G H

/-- Finiteness is derived from that original finite-map base change. -/
theorem actualSmoothRightFinalMap_isFinite : IsFinite (F.tripleToRightImageIncidence G H) :=
  inferInstance

/-- The finite-affine consumer keeps the complete original source fiber and
its actual finite-map stalk action. -/
theorem actualRightOriginalFiberRemainingList
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) :
    (F.rightTargetRemainingList G H (V.2.fromSpec p) s).map
        (FiniteSchemeEuler.originalFiberStalkMap (F.rightIntermediateImageMap G H) V.2 p x).hom =
      (F.rightFiberMiddleList G H (V.2.fromSpec p) s x).map
        ((F.rightSupportMiddlePair G H).stalkMap x.1).hom :=
  F.rightOriginalFiberRemainingList_map G H V p s x

end Motivic.MotivicTest.RightWholeFiberRemainingList
