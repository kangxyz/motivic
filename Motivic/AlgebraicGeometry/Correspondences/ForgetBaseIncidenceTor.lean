/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ForgetBaseIncidence
public import Motivic.Algebra.Homology.TorComparison.AmbientLength
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor
public import Motivic.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.AlgebraicGeometry.Cycles.FundamentalInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Original signed incidence coefficients after forgetting an étale base

The original triple and coefficient schemes are open neighborhoods of the
whole incidence in their forgotten versions. Actual stalk maps identify
categorical Tor in every degree, including every higher correction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open Intersection

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  {f : X ⟶ T} {g : Y ⟶ T} {h : Z ⟶ T}
  [IsSeparated r] [LocallyOfFiniteType r] [FormallyUnramified r]
  [IsSeparated g] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h]
  (A : FiniteCorrespondenceGenerator f g) (B : FiniteCorrespondenceGenerator g h)

omit [FormallyUnramified r] in
/-- The actual triple point equation follows from the original incidence square. -/
theorem forgetBaseIncidencePoint_inclusion (w : A.incidence B) :
    (A.forgetBase r).incidenceInclusion (B.forgetBase r) (A.forgetBaseIncidenceMap r B w) =
      forgetBaseTripleMap r f g h (A.incidenceInclusion B w) :=
  congrArg (fun a : A.incidence B ⟶ correspondenceTripleProduct (f ≫ r) (g ≫ r) (h ≫ r) =>
    a w) (A.forgetBaseIncidenceMap_inclusion r B)

omit [FormallyUnramified r] in
/-- The actual coefficient point equation retains all incidence branches. -/
theorem forgetBaseIncidencePoint_supportProduct (w : A.incidence B) :
    (A.forgetBase r).incidenceToSupportProduct (B.forgetBase r)
        (A.forgetBaseIncidenceMap r B w) =
      A.forgetBaseSupportProductMap r B (A.incidenceToSupportProduct B w) :=
  congrArg (fun a : A.incidence B ⟶ (A.forgetBase r).supportProduct (B.forgetBase r) =>
    a w) (A.forgetBaseIncidenceMap_supportProduct r B)

/-- The ambient scalar isomorphism is induced by the actual open-neighborhood map. -/
def forgetBaseIncidenceAmbientStalkEquiv (w : A.incidence B) :
    (A.forgetBase r).incidenceAmbientStalk (B.forgetBase r)
      (A.forgetBaseIncidenceMap r B w) ≃+* A.incidenceAmbientStalk B w :=
  neighborhoodAmbientStalkEquiv
    (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r))
    ((A.forgetBase r).incidenceInclusion (B.forgetBase r) (A.forgetBaseIncidenceMap r B w))
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (forgetBaseTripleMap r f g h) (forgetBaseAmbientMap r f g h)
    (forgetBaseTripleInclusion_square r f g h) (A.forgetBaseIncidencePoint_inclusion r B w)

/-- Every genuine incidence Tor module is identified through the original scalar map. -/
def forgetBaseIncidenceTorIso (w : A.incidence B) (n : ℕ) :
    (A.forgetBase r).incidenceTor (B.forgetBase r) (A.forgetBaseIncidenceMap r B w) n ≅
      (ModuleCat.restrictScalars (A.forgetBaseIncidenceAmbientStalkEquiv r B w).toRingHom).obj
        (A.incidenceTor B w n) :=
  neighborhoodStalkTorIso
    (correspondenceTripleInclusion (f ≫ r) (g ≫ r) (h ≫ r))
    ((A.forgetBase r).incidenceInclusion (B.forgetBase r) (A.forgetBaseIncidenceMap r B w))
    ((A.forgetBase r).supportProductInclusion (B.forgetBase r))
    ((A.forgetBase r).incidenceToSupportProduct (B.forgetBase r)
      (A.forgetBaseIncidenceMap r B w))
    (point_eq _ _ _ _ ((A.forgetBase r).incidence_ambient_isPullback (B.forgetBase r))
      (A.forgetBaseIncidenceMap r B w))
    (correspondenceTripleInclusion f g h) (A.incidenceInclusion B w)
    (A.supportProductInclusion B) (A.incidenceToSupportProduct B w)
    (point_eq _ _ _ _ (A.incidence_ambient_isPullback B) w)
    (forgetBaseTripleMap r f g h) (A.forgetBaseSupportProductMap r B)
    (forgetBaseAmbientMap r f g h)
    (forgetBaseTripleInclusion_square r f g h) (A.forgetBaseSupportProduct_square r B)
    (A.forgetBaseIncidencePoint_inclusion r B w)
    (A.forgetBaseIncidencePoint_supportProduct r B w) n

/-- Lengths are equal over their respective original ambient rings, degree by degree. -/
theorem forgetBaseIncidenceTor_length (w : A.incidence B) (n : ℕ) :
    Module.length ((A.forgetBase r).incidenceAmbientStalk (B.forgetBase r)
      (A.forgetBaseIncidenceMap r B w))
      ((A.forgetBase r).incidenceTor (B.forgetBase r) (A.forgetBaseIncidenceMap r B w) n) =
        Module.length (A.incidenceAmbientStalk B w) (A.incidenceTor B w n) :=
  (A.forgetBaseIncidenceTorIso r B w n).toLinearEquiv.length_eq.trans
    (TorComparison.length_restrictScalars_of_surjective
      (A.forgetBaseIncidenceAmbientStalkEquiv r B w).toRingHom
      (A.forgetBaseIncidenceAmbientStalkEquiv r B w).surjective _)

variable [IsLocallyNoetherian S] [IsLocallyNoetherian T]
  [LocallyOfFiniteType f] [Flat f] [Smooth g] [Flat h] [Etale r]

/-- The literal signed Tor-Euler coefficient is unchanged; no higher term is discarded. -/
theorem forgetBase_incidenceTorCoefficient (w : genericPoints (A.incidence B)) :
    (A.forgetBase r).incidenceTorCoefficient (B.forgetBase r)
        (mapGenericPoint (A.forgetBaseIncidenceMap r B) w) =
      A.incidenceTorCoefficient B w := by
  unfold incidenceTorCoefficient LengthEuler.signedLengthSum
  apply finsum_congr
  intro n
  simp only [LengthEuler.integerLength, mapGenericPoint, A.forgetBaseIncidenceTor_length r B w.1 n]

end Motivic.FiniteCorrespondenceGenerator
