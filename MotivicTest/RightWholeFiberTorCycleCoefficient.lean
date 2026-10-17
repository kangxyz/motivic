/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorCycleCoefficient

/-!
# Actual right whole-fiber pushforward-cycle consumers

These arbitrary-field smooth-site consumers use the genuine triple-to-right-image
finite map. They retain the original support point and residue degree, explicitly
exercise signed collisions, and identify the fixed-list signed Euler sum with the
actual finite-pushforward triple Tor cycle coefficient at a generic target point.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorCycleCoefficient

variable (k : Type u) [Field k] (X Y Z W : SmoothSite (Spec (.of k)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual remaining inclusion does not alter the residue-degree weight. -/
theorem actualResidueDegree (w : F.tripleIncidence G H) :
    (F.tripleToRightImageIncidence G H).residueDegree w =
      (F.rightIntermediateImageMap G H).residueDegree
        (F.tripleIncidenceToRightSupportProduct G H w) :=
  F.tripleToRightImageIncidence_residueDegree G H w

/-- Every generic triple branch retains its actual original support point under
reindexing the complete fiber over the specified generic image-incidence point. -/
theorem actualGenericFiberPoint
    (y : genericPoints (F.rightImageIncidence G H))
    (w : {w : genericPoints (F.tripleIncidence G H) //
      F.tripleToRightImageIncidence G H w.1 = y.1}) :
    ((F.rightImageIncidenceGenericFiberEquiv G H y).symm w).1 =
      F.tripleIncidenceToRightSupportProduct G H w.1.1 :=
  F.rightImageIncidenceGenericFiberEquiv_symm_apply_val G H y w

/-- Distinct or coincident source points with one target add both signed
contributions with their own literal degrees of the actual finite map. -/
theorem actualSignedCollision (w₁ w₂ : F.tripleIncidence G H)
    (he : F.tripleToRightImageIncidence G H w₁ = F.tripleToRightImageIncidence G H w₂)
    (m n : ℤ) :
    IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
        (Finsupp.single (IntegralClosedSubscheme.pointClosure w₁) m +
          Finsupp.single (IntegralClosedSubscheme.pointClosure w₂) n) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure
        (F.tripleToRightImageIncidence G H w₂))
        (m * ((F.tripleToRightImageIncidence G H).residueDegree w₁ : ℤ) +
          n * ((F.tripleToRightImageIncidence G H).residueDegree w₂ : ℤ)) :=
  IntegralCycle.finitePushforward_two_pointClosures
    (F.tripleToRightImageIncidence G H) w₁ w₂ he m n

/-- The canonical pushed cycle sums all generic source branches over any target;
this does not infer that every source generic has a generic target image. -/
theorem actualTorCycleFiberCoefficient (y : F.rightImageIncidence G H) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y =
      ∑ᶠ w : {w : genericPoints (F.tripleIncidence G H) //
        F.tripleToRightImageIncidence G H w.1 = y},
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 *
          ((F.tripleToRightImageIncidence G H).residueDegree w.1.1 : ℤ) :=
  F.rightImageIncidenceTorCycleCoefficient_eq_finsum k G H y

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

/-- One original fixed regular list gives the actual cycle coefficient, with no
assumed source lift, comparison equality, finite-length input, or degree bound. -/
theorem actualSignedEulerCycleCoefficient
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hs : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler
        (S := Spec (.of k)) G H V p s y hy hp hker n) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y :=
  F.rightFirstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
    k G H V p y hy hp s hs hker

/-- A generic final image-incidence point needs no supplied chart or list to
obtain a signed Euler presentation of its actual finite-pushforward coefficient. -/
theorem actualSignedEulerCycleCoefficient_chart
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H)) :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
      (s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))))
      (_hs : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
      (hker : (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStagePushforwardRemainingEuler
          (S := Spec (.of k)) G H V p s y hy hp hker n) =
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
            (F.tripleIncidenceTorCycle k G H)) y :=
  F.exists_rightFirstStageRemainingEuler_finitePushforward_chart k G H y hy

end Motivic.MotivicTest.RightWholeFiberTorCycleCoefficient
