/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorRemainingProjection
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Original finite-map remaining projection on actual smooth correspondences

The actual global pushforward stalk and every original fiber point retain the
same common remaining list. Smooth finite-type geometry derives all Noetherian
hypotheses. Generic final image-incidence points give the entire whole finite
homology premise, and an actual chart and common list can be chosen internally.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorRemainingProjection

open LengthEuler

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The literal six-factor ambient is locally Noetherian by smooth finite-type geometry. -/
local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

/-- The actual intermediate image product is locally Noetherian: its image is
closed in the smooth product and its first-support product is locally finite type. -/
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

/-- The actual chain comparison has the original inverse on each module degree. -/
theorem actualRemainingProjection_inverse (n r : ℕ) :
    (F.rightFirstStageWholePushforwardRemainingIso (S := Spec (.of K)) G H V p s n).hom.f r ≫
      (F.rightFirstStageWholePushforwardRemainingIso (S := Spec (.of K)) G H V p s n).inv.f r =
        𝟙 _ := by
  exact congrArg (fun a => a.f r)
    (F.rightFirstStageWholePushforwardRemainingIso (S := Spec (.of K)) G H V p s n).hom_inv_id

/-- Actual smooth correspondences satisfy the per-degree original global
pushforward Euler formula, without any local or whole finite-homology premise. -/
theorem actualSmoothRemainingProjection
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    let hwhole := F.rightFirstStageWholeRemaining_finiteHomology
      (S := Spec (.of K)) G H V p y hy hp s hs n
    chainEuler (F.rightFirstStagePushforwardRemainingKoszul (S := Spec (.of K)) G H V p s n)
        (F.rightFirstStagePushforwardRemaining_finiteHomology
          (S := Spec (.of K)) G H V p s n hwhole) =
      ∑ᶠ x : {w : F.rightIntermediateSupportProduct G H //
        F.rightIntermediateImageMap G H w = V.2.fromSpec p},
        ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          chainEuler (F.rightFirstStageSourceRemainingKoszul (S := Spec (.of K)) G H V p s x n)
            (F.rightFirstStageSourceRemaining_finiteHomology
              (S := Spec (.of K)) G H V p s n hwhole x) :=
  F.rightFirstStageRemainingProjectionEuler (S := Spec (.of K)) G H V p y hy hp s hs n

/-- The affine chart, coordinate point and single smooth diagonal list are
constructed from the original final image generic point for the entire Euler family. -/
theorem actualSmoothRemainingProjection_chart
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H)) :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
      (s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s ∧
      ∀ n,
        let hwhole := F.rightFirstStageWholeRemaining_finiteHomology
          (S := Spec (.of K)) G H V p y hy hp s hs n;
        chainEuler (F.rightFirstStagePushforwardRemainingKoszul (S := Spec (.of K)) G H V p s n)
            (F.rightFirstStagePushforwardRemaining_finiteHomology
              (S := Spec (.of K)) G H V p s n hwhole) =
          ∑ᶠ x : {w : F.rightIntermediateSupportProduct G H //
            F.rightIntermediateImageMap G H w = V.2.fromSpec p},
            ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
              chainEuler (F.rightFirstStageSourceRemainingKoszul
                (S := Spec (.of K)) G H V p s x n)
                (F.rightFirstStageSourceRemaining_finiteHomology
                  (S := Spec (.of K)) G H V p s n hwhole x) := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_rightFirstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy
  exact ⟨V, p, hp, s, hs, hreg,
    fun n => actualSmoothRemainingProjection K X Y Z W F G H V p s y hy hp hs n⟩

end Motivic.MotivicTest.RightWholeFiberTorRemainingProjection
