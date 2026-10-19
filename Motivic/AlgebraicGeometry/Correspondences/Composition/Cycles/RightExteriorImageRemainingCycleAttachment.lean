/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightExteriorImageRemainingTorAttachment
public import Motivic.AlgebraicGeometry.Correspondences.Exterior.RightImage.RemainingLiftCases
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward

/-!
# The right remaining quotient as an actual pushed incidence Tor coefficient

Fix one integral support C in the actual G,H image and a generator P with
that literal image ideal. The actual map F.incidence P into the right whole
image incidence is a proved closed immersion. Its finite generic pushforward
sum has a unique contribution over any specified lift, with residue degree
one. This uniqueness concerns only this remaining closed immersion: original
G,H labels may collide in their images and are not identified or discarded.

At a generic right image-incidence point, the literal full exterior quotient
Euler equals the coefficient of the actual pushed F,P incidence Tor cycle.
The fixed arbitrary target point, original stalk scalars, same regular Y list,
and exact diagonal-kernel presentation are retained. With no generic lift,
both the same-list quotient Euler and the actual finite pushforward vanish.
The full exterior may be nonreduced. No off-generic statement, global cycle
equality, right bracket, or correspondence identity is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open scoped BigOperators

universe u

namespace Motivic.RightExteriorImageRemainingCycleAttachment
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

open RightExteriorImageComponentGeometry
open RightExteriorImageRemainingTorAttachment
open _root_.HomologicalComplex.ModuleLengthEuler

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (C : IntegralClosedSubscheme (G.incidenceMap H).image)
  (P : FiniteCorrespondenceGenerator Y.hom W.hom)
  (hC : (C.val.subschemeι ≫ (G.incidenceMap H).imageι).ker = P.val)

local instance structureBaseNoetherian :
    IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
  inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))

local instance sourceNoetherian : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance actualIncidenceNoetherian : IsNoetherian (F.incidence P) :=
  isNoetherian_of_finiteType (F.incidenceSource P)

/-- Only the actual remaining closed immersion has a unique contribution
above a specified generic lift, with residue degree one. -/
theorem remainingToImage_TorCoefficient_of_genericLift
    (w : genericPoints (F.incidence P)) (y : F.rightImageIncidence G H)
    (hwy : remainingToImage F G H C P hC w.1 = y) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
        (IntegralCycle.ofGenericCoefficients (F.incidence P) (F.incidenceTorCoefficient P))) y =
      F.incidenceTorCoefficient P w := by
  classical
  let actualGenericPointFintype := IntegralCycle.genericPointFintype (F.incidence P)
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
    (y : F.rightImageIncidence G H)
    (hno : ¬ ∃ w : genericPoints (F.incidence P), remainingToImage F G H C P hC w.1 = y) :
    IntegralCycle.toPoints
      (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
        (IntegralCycle.ofGenericCoefficients (F.incidence P) (F.incidenceTorCoefficient P))) y =
      0 := by
  classical
  let actualGenericPointFintype := IntegralCycle.genericPointFintype (F.incidence P)
  rw [IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  apply Finset.sum_eq_zero
  intro w _
  exact ite_eq_right (fun hw => hno ⟨w, hw⟩)

local instance imageProductNoetherian : IsNoetherian (F.rightIntermediateImageProduct G H) :=
  RightExteriorImageRemainingTorAttachment.imageProductNoetherian F G H

/-- The same original regular middle list at the same fixed image-product
point computes the coefficient of the actual pushed remaining incidence Tor
cycle, including the absent-lift case. The literal full quotient and its
Artinian-support finite-homology witness are kept unchanged. -/
theorem remainingQuotientEuler_eq_finitePushforward_coefficient
    (y : genericPoints (F.rightImageIncidence G H))
    (x : F.rightIntermediateImageProduct G H)
    (hp : x = F.rightImageIncidenceInclusion G H y.1)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H x)))
    (hsreg : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (F.rightImageMiddlePair G H x)) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk (F.rightImageMiddlePair G H x) = Ideal.ofList s) :
    letI := F.rightTargetRemainingList_support_isArtinian G H x y.1 y.2 hp s hker
    chainEuler (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of ((F.rightIntermediateImageProduct G H).presheaf.stalk x)
        (((F.rightIntermediateImageProduct G H).presheaf.stalk x) ⧸
          (F.rightImageComponentExteriorInclusion G H C).ker.stalk x))
      (F.rightTargetRemainingList G H x s))
      (_root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
          bot_le) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (remainingToImage F G H C P hC)
          (IntegralCycle.ofGenericCoefficients (F.incidence P)
            (F.incidenceTorCoefficient P))) y.1 := by
  classical
  let := F.rightTargetRemainingList_support_isArtinian G H x y.1 y.2 hp s hker
  by_cases hlift : ∃ w : genericPoints (F.incidence P),
      remainingToImage F G H C P hC w.1 = y.1
  · obtain ⟨w, hwy⟩ := hlift
    exact (remainingQuotientEuler_eq_incidenceTorCoefficient_fixedPoint
      F G H C P hC w x y.1 y.2 hp hwy s hsreg hker).trans
        (remainingToImage_TorCoefficient_of_genericLift F G H C P hC w y.1 hwy).symm
  · rw [remainingToImage_TorCoefficient_zero_of_no_genericLift F G H C P hC y.1 hlift]
    subst x
    exact remainingQuotient_chainEuler_zero_of_no_genericLift F G H C P hC y hlift s

end Motivic.RightExteriorImageRemainingCycleAttachment
