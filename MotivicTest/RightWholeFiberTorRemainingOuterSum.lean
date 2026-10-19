/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorRemainingOuterSum
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Actual finite outer projection for smooth-site correspondences

All outer bounds, finite supports and remaining finite lengths are derived
from the original smooth geometry, actual whole coefficient and final image
generic point. The selected chart and one remaining diagonal list serve every
outer degree and every original source-fiber point.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorRemainingOuterSum
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

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

/-- Original smooth geometry proves one bound for all genuine numerical Euler branches. -/
theorem actualOuterEuler_bound :
    ∃ b : ℕ, ∀ r, b ≤ r →
      F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs r = 0 ∧
      ∀ x, F.rightFirstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x r = 0 :=
  F.rightFirstStageRemainingEuler_exists_bound (S := Spec (.of K)) G H V p s y hy hp hs

/-- The full outer projection sum uses actual finite supports and scheme residue degrees. -/
theorem actualOuterProjection :
    (∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
      F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs r) =
    ∑ᶠ x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p},
      ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        ∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
          F.rightFirstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x r :=
  F.rightFirstStageRemainingOuterProjectionEuler (S := Spec (.of K)) G H V p s y hy hp hs

/-- A chart and single regular list are constructed from the original final image
generic point, and the resulting actual outer projection sum is genuinely finite. -/
theorem actualOuterProjection_chart :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
      (s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
      Function.HasFiniteSupport
        (F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs) ∧
      (∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
        F.rightFirstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs r) =
      ∑ᶠ x : {w : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H w = V.2.fromSpec p},
        ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          ∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
            F.rightFirstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x r := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_rightFirstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy
  exact ⟨V, p, hp, s, hs, hreg,
    F.rightFirstStagePushforwardRemainingEuler_finiteSupport
      (S := Spec (.of K)) G H V p s y hy hp hs,
    actualOuterProjection K X Y Z W F G H V p s y hy hp hs⟩

end Motivic.MotivicTest.RightWholeFiberTorRemainingOuterSum
