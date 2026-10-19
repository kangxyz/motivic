/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ExteriorImageRemainingTorAttachment
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Image.RemainingLiftCases
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward

/-!
# The remaining exterior quotient as an actual pushed Tor-cycle coefficient

Fix one integral support in the actual intermediate image and a correspondence
generator identified by their literal image ideals. The resulting remaining
incidence map is a proved closed immersion. Its finite generic pushforward sum
therefore has at most one contribution, whose residue degree is one. This
argument concerns only that component's remaining closed immersion; it makes
no injectivity assertion for either original finite image map.

At a generic whole-image-incidence point, the full exterior quotient Euler
equals that actual pushed incidence Tor-cycle coefficient. A genuine generic
lift uses the fixed-point Tor attachment. With no lift, both the quotient
Euler and the finite pushforward coefficient vanish. The original point,
scalar action, middle list, and full nonreduced exterior quotient are retained.
No global cycle equality or correspondence composition identity is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open scoped BigOperators

universe u

namespace Motivic.ExteriorImageRemainingCycleAttachment
open _root_.AlgebraicGeometry.Scheme

open ExteriorImageComponentGeometry
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.Motivic.ExteriorImageRemainingTorAttachment
open _root_.HomologicalComplex.ModuleLengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (F.incidenceMap G).image)
  (P : FiniteCorrespondenceGenerator X.hom Z.hom)
  (hC : (C.val.subschemeι ≫ (F.incidenceMap G).imageι).ker = P.val)

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

/-- Only the actual remaining closed immersion has a unique contribution
above a specified generic lift, with residue degree one. -/
theorem remainingToImage_TorCoefficient_of_genericLift
    (w : genericPoints (P.incidence H)) (y : F.leftImageIncidence G H)
    (hwy : remainingToImage F G H C P hC w.1 = y) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
        (IntegralCycle.ofGenericCoefficients (P.incidence H) (P.incidenceTorCoefficient H))) y =
      P.incidenceTorCoefficient H w := by
  classical
  let := IntegralCycle.genericPointFintype (P.incidence H)
  rw [IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  rw [Finset.sum_eq_single w]
  · rw [ite_eq_left hwy, residueDegree_of_surjectiveOnStalks]
    simp only [Nat.cast_one, mul_one]
  · intro v _ hv
    have hne : remainingToImage F G H C P hC v.1 ≠ y := by
      intro hvy
      exact hv (Subtype.ext ((remainingToImage F G H C P hC).isEmbedding.injective
        (hvy.trans hwy.symm)))
    simp only [ite_eq_right hne]
  · simp

/-- Without a generic source lift, every term of the existing finite generic
pushforward sum is zero; no point is inserted into an empty fiber. -/
theorem remainingToImage_TorCoefficient_zero_of_no_genericLift
    (y : F.leftImageIncidence G H)
    (hno : ¬ ∃ w : genericPoints (P.incidence H), remainingToImage F G H C P hC w.1 = y) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
        (IntegralCycle.ofGenericCoefficients (P.incidence H) (P.incidenceTorCoefficient H))) y =
      0 := by
  classical
  let := IntegralCycle.genericPointFintype (P.incidence H)
  rw [IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  apply Finset.sum_eq_zero
  intro w _
  exact ite_eq_right (fun hw => hno ⟨w, hw⟩)

local instance imageProductNoetherian : IsNoetherian (F.leftIntermediateImageProduct G H) :=
  ExteriorImageComponentEulerReplacement.imageProductNoetherian F G H

/-- The same original regular middle list at the same fixed image-product
point computes the coefficient of the actual pushed remaining incidence Tor
cycle, including the absent-lift case. The literal full quotient and its
Artinian-support finite-homology witness are kept unchanged. -/
theorem remainingQuotientEuler_eq_finitePushforward_coefficient
    (y : genericPoints (F.leftImageIncidence G H))
    (x : F.leftIntermediateImageProduct G H)
    (hp : x = F.leftImageIncidenceInclusion G H y.1)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk (F.leftImageMiddlePair G H x)))
    (hsreg : IsRegular ((pullback Z.hom Z.hom).presheaf.stalk (F.leftImageMiddlePair G H x)) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk (F.leftImageMiddlePair G H x) = Ideal.ofList s) :
    letI := F.leftTargetRemainingList_support_isArtinian G H x y.1 y.2 hp s hker
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.leftIntermediateImageProduct G H).presheaf.stalk x)
        (((F.leftIntermediateImageProduct G H).presheaf.stalk x) ⧸
          (exteriorInclusion F G H C).ker.stalk x))
      (F.leftTargetRemainingList G H x s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
          (IntegralCycle.ofGenericCoefficients (P.incidence H)
            (P.incidenceTorCoefficient H))) y.1 := by
  classical
  let := F.leftTargetRemainingList_support_isArtinian G H x y.1 y.2 hp s hker
  by_cases hlift : ∃ w : genericPoints (P.incidence H),
      remainingToImage F G H C P hC w.1 = y.1
  · obtain ⟨w, hwy⟩ := hlift
    exact (remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
      F G H C P hC w x y.1 y.2 hp hwy s hsreg hker).trans
        (remainingToImage_TorCoefficient_of_genericLift F G H C P hC w y.1 hwy).symm
  · rw [remainingToImage_TorCoefficient_zero_of_no_genericLift F G H C P hC y.1 hlift]
    subst x
    exact remainingQuotient_chainEuler_zero_of_no_genericLift F G H C P hC y hlift s

end Motivic.ExteriorImageRemainingCycleAttachment
