/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorRemainingProjection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

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

namespace Motivic.MotivicTest.WholeFiberTorRemainingProjection
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open _root_.HomologicalComplex.ModuleLengthEuler

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
closed in the smooth product and its third-support product is locally finite type. -/
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

/-- The actual chain comparison has the original inverse on each module degree. -/
theorem actualRemainingProjection_inverse (n r : ℕ) :
    (F.firstStageWholePushforwardRemainingIso (S := Spec (.of K)) G H V p s n).hom.f r ≫
      (F.firstStageWholePushforwardRemainingIso (S := Spec (.of K)) G H V p s n).inv.f r = 𝟙 _ := by
  exact congrArg (fun a => a.f r)
    (F.firstStageWholePushforwardRemainingIso (S := Spec (.of K)) G H V p s n).hom_inv_id

/-- Actual smooth correspondences satisfy the per-degree original global
pushforward Euler formula, without any local or whole finite-homology premise. -/
theorem actualSmoothRemainingProjection
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (hs : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    let hwhole := F.firstStageWholeRemaining_finiteHomology
      (S := Spec (.of K)) G H V p y hy hp s hs n
    chainEuler (F.firstStagePushforwardRemainingKoszul (S := Spec (.of K)) G H V p s n)
        (F.firstStagePushforwardRemaining_finiteHomology
          (S := Spec (.of K)) G H V p s n hwhole) =
      ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = V.2.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          chainEuler (F.firstStageSourceRemainingKoszul (S := Spec (.of K)) G H V p s x n)
            (F.firstStageSourceRemaining_finiteHomology
              (S := Spec (.of K)) G H V p s n hwhole x) :=
  F.firstStageRemainingProjectionEuler (S := Spec (.of K)) G H V p y hy hp s hs n

/-- The affine chart, coordinate point and single smooth diagonal list are
constructed from the original final image generic point for the entire Euler family. -/
theorem actualSmoothRemainingProjection_chart
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H)) :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))))
      (hs : (pullback.diagonal Z.hom).ker.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))) s ∧
      ∀ n,
        let hwhole := F.firstStageWholeRemaining_finiteHomology
          (S := Spec (.of K)) G H V p y hy hp s hs n;
        chainEuler (F.firstStagePushforwardRemainingKoszul (S := Spec (.of K)) G H V p s n)
            (F.firstStagePushforwardRemaining_finiteHomology
              (S := Spec (.of K)) G H V p s n hwhole) =
          ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
            F.leftIntermediateImageMap G H w = V.2.fromSpec p},
            ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
              chainEuler (F.firstStageSourceRemainingKoszul
                (S := Spec (.of K)) G H V p s x n)
                (F.firstStageSourceRemaining_finiteHomology
                  (S := Spec (.of K)) G H V p s n hwhole x) := by
  obtain ⟨V, p, hp, s, hreg, hs, _⟩ :=
    F.exists_firstStageWholeRemaining_chart (S := Spec (.of K)) G H y hy
  exact ⟨V, p, hp, s, hs, hreg,
    fun n => actualSmoothRemainingProjection K X Y Z W F G H V p s y hy hp hs n⟩

end Motivic.MotivicTest.WholeFiberTorRemainingProjection
