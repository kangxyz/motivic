/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityTorLengthComparison
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-! # Actual exterior Tor degrees and generic coefficients retain the whole local fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityTorLengthComparison

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

example
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) (n : ℕ) :
    Module.length
      ((A.exteriorIdentityGenerator T).incidenceAmbientStalk (B.exteriorIdentityGenerator T) w)
      ((A.exteriorIdentityGenerator T).incidenceTor (B.exteriorIdentityGenerator T) w n) =
      Module.length (A.incidenceAmbientStalk B (A.exteriorIncidenceOriginalCoordinate B T w))
        (A.incidenceTor B (A.exteriorIncidenceOriginalCoordinate B T w) n) *
      Module.length
        (((A.exteriorIdentityGenerator T).incidence
          (B.exteriorIdentityGenerator T)).presheaf.stalk w)
        (Koszul.coefficientClosedFiber
          ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap w).hom) :=
  A.exteriorIncidenceTor_length B T w n

example
    (w : genericPoints ((A.exteriorIdentityGenerator T).incidence
      (B.exteriorIdentityGenerator T))) :
    (A.exteriorIdentityGenerator T).incidenceTorCoefficient (S := Spec (.of k))
        (B.exteriorIdentityGenerator T) w =
      A.incidenceTorCoefficient (S := Spec (.of k)) B (A.exteriorIncidenceOriginalGeneric B T w) *
        A.exteriorIncidenceFiberMultiplicity B T w :=
  A.exteriorIncidenceTorCoefficient_eq B T w

end MotivicTest.ExteriorIdentityTorLengthComparison
