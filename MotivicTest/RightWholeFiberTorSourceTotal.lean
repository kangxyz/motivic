/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorSourceTotal
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual fixed-list source-total attachment for smooth-site correspondences

The original full-fiber supported-Tor outer Euler sum is attached to the
canonical triple total with its actual differentials. All remaining lengths
and degree bounds are proved from the original geometry.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorSourceTotal

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of K)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
  (s : List ((pullback Y.hom Y.hom).presheaf.stalk
    (F.rightImageMiddlePair G H (V.2.fromSpec p))))
  (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
  (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
  (hs : (pullback.diagonal Y.hom).ker.stalk
    (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)


variable (hreg : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
  (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)

include hreg in
/-- The same original source branch and fixed image list compute the canonical
triple coefficient through the actual bounded total, over an arbitrary field. -/
theorem actualSourceTotal
    (w : F.tripleIncidence G H)
    (hw : F.rightIntermediateImageMap G H (F.tripleIncidenceToRightSupportProduct G H w) =
      V.2.fromSpec p)
    (hgen : w ∈ genericPoints (F.tripleIncidence G H)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs ⟨_, hw⟩ n) =
      F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H ⟨w, hgen⟩ :=
  F.rightFirstStageSourceRemainingEuler_eq_tripleCoefficient
    (S := Spec (.of K)) G H w V p y hy hp hw hgen s hreg hs

include hreg in
/-- No source lift or genericity witness is assumed for an arbitrary original
fiber point: the genuine lift and canonical coefficient equality are constructed. -/
theorem actualEveryBranchTotal
    (x : {v : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H v = V.2.fromSpec p}) :
    ∃ q : genericPoints (F.tripleIncidence G H),
      F.tripleIncidenceToRightSupportProduct G H q.1 = x.1 ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x n) =
        F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H q :=
  F.rightFirstStageSourceRemainingEuler_exists_tripleLift
    (S := Spec (.of K)) G H V p y hy hp s hreg hs x

include hreg in
/-- The original finite projection's complete source side is the actual canonical
triple coefficient, with every original residue weight preserved. -/
theorem actualWholeFiberTotalProjection :
    ∃ lift : {v : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H v = V.2.fromSpec p} →
        genericPoints (F.tripleIncidence G H),
      (∀ x, F.tripleIncidenceToRightSupportProduct G H (lift x).1 = x.1) ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
      ∑ᶠ x : {v : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H v = V.2.fromSpec p},
        ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H (lift x) :=
  F.rightFirstStageRemainingProjection_to_tripleCoefficient
    (S := Spec (.of K)) G H V p y hy hp s hreg hs

/-- An arbitrary final image generic point supplies its own affine chart and
one regular middle list for the entire genuine source-total projection. -/
theorem actualWholeFiberTotalProjection_chart :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
      (s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      ∃ lift : {v : F.rightIntermediateSupportProduct G H //
          F.rightIntermediateImageMap G H v = V.2.fromSpec p} →
          genericPoints (F.tripleIncidence G H),
        (∀ x, F.tripleIncidenceToRightSupportProduct G H (lift x).1 = x.1) ∧
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
        ∑ᶠ x : {v : F.rightIntermediateSupportProduct G H //
          F.rightIntermediateImageMap G H v = V.2.fromSpec p},
          ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
            F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H (lift x) := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_rightFirstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy
  exact ⟨V, p, hp, s, hs,
    actualWholeFiberTotalProjection K X Y Z W F G H V p s y hy hp hs hreg⟩

end Motivic.MotivicTest.RightWholeFiberTorSourceTotal
