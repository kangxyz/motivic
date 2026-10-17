/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorRemainingFiber
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Entire actual final-incidence fiber consumers over arbitrary fields

These consumers retain every original point in the finite image-product fiber.
They derive its generic triple-incidence lifts and choose one actual remaining
middle list giving finite supported-Tor Koszul homology on every branch and in
every first-stage degree. No local support, length, or source-genericity input
is substituted for the geometry.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Motivic.Intersection

universe u

namespace MotivicTest.WholeFiberTorRemainingFiber

variable (K : Type u) [Field K]
  (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of K)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of K))
    X.hom Y.hom Z.hom W.hom

/-- The whole point fiber is the actual fiber of a finite morphism between
the original final-incidence schemes, without a ring product decomposition. -/
def actualImageIncidenceFiberEquiv (y : F.leftImageIncidence G H) :
    {w : F.tripleIncidence G H // F.tripleToLeftImageIncidence G H w = y} ≃
      {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y} :=
  F.leftImageIncidenceFiberEquiv G H y

/-- Every original finite-fiber branch over an actual generic final image point
has a genuinely generic triple-incidence lift with both original projections. -/
theorem actualImageIncidenceFiber_genericLift
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (x : F.leftIntermediateSupportProduct G H)
    (hx : F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y) :
    ∃ w : F.tripleIncidence G H, w ∈ genericPoints (F.tripleIncidence G H) ∧
      F.tripleToLeftImageIncidence G H w = y ∧
        F.tripleIncidenceToLeftSupportProduct G H w = x :=
  F.leftImageIncidenceFiber_lift_generic G H y hy x hx

/-- Over every field one actual middle list simultaneously gives finite
remaining homology on all genuine supported-Tor source branches and degrees. -/
theorem exists_actualAllFiberSupportedFiniteHomology
    (U : (F.leftIntermediateImageProduct G H).affineOpens)
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hyU : F.leftImageIncidenceInclusion G H y ∈ U.1) :
    ∃ s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y))),
      RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y))) s ∧
      (pullback.diagonal Z.hom).ker.stalk
        (F.leftImageMiddlePair G H (F.leftImageIncidenceInclusion G H y)) = Ideal.ofList s ∧
      ∀ (x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y}) (n : ℕ),
        LengthEuler.FiniteHomology
          (Koszul.coefficientComplex
            (closedIntersectionSupportedStalkTor
              (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
              (F.tripleSupportProductInclusion G H) (F.leftIntermediateSupportInclusion G H)
              (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
              x.1 n)
            ((F.leftFiberMiddleList G H (F.leftImageIncidenceInclusion G H y) s x).map
              ((F.leftSupportMiddlePair G H).stalkMap x.1).hom)) := by
  obtain ⟨s, hs, hker, _⟩ :=
    F.exists_leftWholeFiberTorRemainingFiber_finiteHomology G H U y hy hyU
  exact ⟨s, hs, hker, F.leftSupportedTorRemainingFiber_finiteHomology G H U y hy hyU s hker⟩

end MotivicTest.WholeFiberTorRemainingFiber
