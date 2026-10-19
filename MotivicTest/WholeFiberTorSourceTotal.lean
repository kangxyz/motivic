/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorSourceTotal
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

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

namespace Motivic.MotivicTest.WholeFiberTorSourceTotal
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian (F.leftIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of K)) X.hom
  have : IsLocallyNoetherian (pullback X.hom Z.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Z.hom)
  have : IsLocallyNoetherian (F.incidenceMap G).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback X.hom Z.hom)
      (F.incidenceMap G).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (F.incidenceMap G).image)
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom))

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
  (s : List ((pullback Z.hom Z.hom).presheaf.stalk
    (F.leftImageMiddlePair G H (V.2.fromSpec p))))
  (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
  (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
  (hs : (pullback.diagonal Z.hom).ker.stalk
    (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)


variable (hreg : RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
  (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)

include hreg in
/-- The same original source branch and fixed image list compute the canonical
triple coefficient through the actual bounded total, over an arbitrary field. -/
theorem actualSourceTotal
    (w : F.tripleIncidence G H)
    (hw : F.leftIntermediateImageMap G H (F.tripleIncidenceToLeftSupportProduct G H w) =
      V.2.fromSpec p)
    (hgen : w ∈ genericPoints (F.tripleIncidence G H)) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs ⟨_, hw⟩ n) =
      F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H ⟨w, hgen⟩ :=
  F.firstStageSourceRemainingEuler_eq_tripleCoefficient
    (S := Spec (.of K)) G H w V p y hy hp hw hgen s hreg hs

include hreg in
/-- No source lift or genericity witness is assumed for an arbitrary original
fiber point: the genuine lift and canonical coefficient equality are constructed. -/
theorem actualEveryBranchTotal
    (x : {v : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H v = V.2.fromSpec p}) :
    ∃ q : genericPoints (F.tripleIncidence G H),
      F.tripleIncidenceToLeftSupportProduct G H q.1 = x.1 ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.firstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x n) =
        F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H q :=
  F.firstStageSourceRemainingEuler_exists_tripleLift
    (S := Spec (.of K)) G H V p y hy hp s hreg hs x

include hreg in
/-- The original finite projection's complete source side is the actual canonical
triple coefficient, with every original residue weight preserved. -/
theorem actualWholeFiberTotalProjection :
    ∃ lift : {v : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H v = V.2.fromSpec p} →
        genericPoints (F.tripleIncidence G H),
      (∀ x, F.tripleIncidenceToLeftSupportProduct G H (lift x).1 = x.1) ∧
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
      ∑ᶠ x : {v : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H v = V.2.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H (lift x) :=
  F.firstStageRemainingProjection_to_tripleCoefficient
    (S := Spec (.of K)) G H V p y hy hp s hreg hs

/-- An arbitrary final image generic point supplies its own affine chart and
one regular middle list for the entire genuine source-total projection. -/
theorem actualWholeFiberTotalProjection_chart :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Z.hom).ker.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      ∃ lift : {v : F.leftIntermediateSupportProduct G H //
          F.leftIntermediateImageMap G H v = V.2.fromSpec p} →
          genericPoints (F.tripleIncidence G H),
        (∀ x, F.tripleIncidenceToLeftSupportProduct G H (lift x).1 = x.1) ∧
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs n) =
        ∑ᶠ x : {v : F.leftIntermediateSupportProduct G H //
          F.leftIntermediateImageMap G H v = V.2.fromSpec p},
          ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
            F.tripleIncidenceTorCoefficient (S := Spec (.of K)) G H (lift x) := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_firstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy
  exact ⟨V, p, hp, s, hs,
    actualWholeFiberTotalProjection K X Y Z W F G H V p s y hy hp hs hreg⟩

end Motivic.MotivicTest.WholeFiberTorSourceTotal
