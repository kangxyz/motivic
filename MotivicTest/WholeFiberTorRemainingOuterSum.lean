/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorRemainingOuterSum
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

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

namespace Motivic.MotivicTest.WholeFiberTorRemainingOuterSum

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

/-- Original smooth geometry proves one bound for all genuine numerical Euler branches. -/
theorem actualOuterEuler_bound :
    ∃ b : ℕ, ∀ r, b ≤ r →
      F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs r = 0 ∧
      ∀ x, F.firstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x r = 0 :=
  F.firstStageRemainingEuler_exists_bound (S := Spec (.of K)) G H V p s y hy hp hs

/-- The full outer projection sum uses actual finite supports and scheme residue degrees. -/
theorem actualOuterProjection :
    (∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
      F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs r) =
    ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p},
      ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        ∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
          F.firstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x r :=
  F.firstStageRemainingOuterProjectionEuler (S := Spec (.of K)) G H V p s y hy hp hs

/-- A chart and single regular list are constructed from the original final image
generic point, and the resulting actual outer projection sum is genuinely finite. -/
theorem actualOuterProjection_chart :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Z.hom).ker.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))) s ∧
      Function.HasFiniteSupport
        (F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs) ∧
      (∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
        F.firstStagePushforwardRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs r) =
      ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = V.2.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          ∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
            F.firstStageSourceRemainingEuler (S := Spec (.of K)) G H V p s y hy hp hs x r := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_firstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy
  exact ⟨V, p, hp, s, hs, hreg,
    F.firstStagePushforwardRemainingEuler_finiteSupport
      (S := Spec (.of K)) G H V p s y hy hp hs,
    actualOuterProjection K X Y Z W F G H V p s y hy hp hs⟩

end Motivic.MotivicTest.WholeFiberTorRemainingOuterSum
