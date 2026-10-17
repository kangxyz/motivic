/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityRemainingIncidence
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-! # Consumers of the actual exterior coefficient and remaining incidence squares -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityRemainingIncidence

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

example :
    IsPullback (A.exteriorCoefficientQuotientInclusion B T)
      (A.exteriorParameterDiagonalInclusion T B)
      (exteriorAmbientParameterInclusion X Y Z T)
      ((A.exteriorIdentityGenerator T).supportProductInclusion
        (B.exteriorIdentityGenerator T)) :=
  A.exteriorCoefficientQuotientInclusion_isPullback B T

example :
    IsPullback
      ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T))
      (A.exteriorIncidenceToCoefficientQuotient B T)
      (exteriorAmbientRemainingInclusion X Y Z T)
      (A.exteriorCoefficientQuotientInclusion B T) :=
  A.exteriorRemainingIncidence_isPullback B T

example :
    A.exteriorIncidenceToCoefficientQuotient B T ≫
        A.exteriorCoefficientQuotientProjection B T =
      A.exteriorIncidenceOriginalCoordinate B T ≫ A.incidenceToSupportProduct B :=
  A.exteriorIncidenceToCoefficientQuotient_projection B T

omit [GeometricallyIntegral T.hom] in
example (n : ℕ) :
    IsClosedImmersion
      (A.exteriorIncidenceToCoefficientQuotient B (AlgebraicSimplex.smoothSiteObj k n)) :=
  inferInstance

end MotivicTest.ExteriorIdentityRemainingIncidence
