/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityCoefficientAmbient

/-!
# The actual exterior incidence after the parameter quotient

The full exterior incidence maps to the actual coefficient parameter quotient.
It remains the Cartesian intersection with the remaining ambient diagonal.
This retains the exact source, coefficient, and nilpotent incidence schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The actual exterior incidence in the coefficient parameter quotient. -/
def exteriorIncidenceToCoefficientQuotient :
    (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T) ⟶
      A.exteriorParameterDiagonal T B :=
  (A.exteriorCoefficientQuotientInclusion_isPullback B T).lift
    ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) ≫
      exteriorAmbientRemainingInclusion X Y Z T)
    ((A.exteriorIdentityGenerator T).incidenceToSupportProduct (B.exteriorIdentityGenerator T))
    (by
      simpa only [Category.assoc, exteriorAmbientRemainingInclusion_parameterInclusion] using
        (A.exteriorIdentityGenerator T).incidence_ambient_comm (B.exteriorIdentityGenerator T))

@[reassoc (attr := simp)]
theorem exteriorIncidenceToCoefficientQuotient_inclusion :
    A.exteriorIncidenceToCoefficientQuotient B T ≫ A.exteriorCoefficientQuotientInclusion B T =
      (A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) ≫
        exteriorAmbientRemainingInclusion X Y Z T :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceToCoefficientQuotient_parameterInclusion :
    A.exteriorIncidenceToCoefficientQuotient B T ≫ A.exteriorParameterDiagonalInclusion T B =
      (A.exteriorIdentityGenerator T).incidenceToSupportProduct (B.exteriorIdentityGenerator T) :=
  IsPullback.lift_snd _ _ _ _

/-- Removing the common parameter block preserves the actual Cartesian incidence square. -/
theorem exteriorRemainingIncidence_isPullback :
    IsPullback
      ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T))
      (A.exteriorIncidenceToCoefficientQuotient B T)
      (exteriorAmbientRemainingInclusion X Y Z T)
      (A.exteriorCoefficientQuotientInclusion B T) := by
  apply IsPullback.of_bot
    (v₂₁ := A.exteriorParameterDiagonalInclusion T B)
    (v₂₂ := exteriorAmbientParameterInclusion X Y Z T)
  · simpa only [exteriorIncidenceToCoefficientQuotient_parameterInclusion,
      exteriorAmbientRemainingInclusion_parameterInclusion] using
      (A.exteriorIdentityGenerator T).incidence_ambient_isPullback
        (B.exteriorIdentityGenerator T)
  · exact (A.exteriorIncidenceToCoefficientQuotient_inclusion B T).symm
  · exact A.exteriorCoefficientQuotientInclusion_isPullback B T

instance exteriorIncidenceToCoefficientQuotient_isClosedImmersion :
    IsClosedImmersion (A.exteriorIncidenceToCoefficientQuotient B T) :=
  MorphismProperty.of_isPullback (A.exteriorRemainingIncidence_isPullback B T) inferInstance

/-- Forgetting the parameter preserves the literal coefficient support coordinates. -/
@[reassoc]
theorem exteriorIncidenceToCoefficientQuotient_projection :
    A.exteriorIncidenceToCoefficientQuotient B T ≫
        A.exteriorCoefficientQuotientProjection B T =
      A.exteriorIncidenceOriginalCoordinate B T ≫ A.incidenceToSupportProduct B := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorCoefficientQuotientProjection_fst,
      exteriorIncidenceToCoefficientQuotient_parameterInclusion_assoc,
      incidenceToSupportProduct_fst_assoc, incidenceToSupportProduct_fst,
      exteriorIncidenceOriginalCoordinate_fst, exteriorIncidenceFirstCoordinate]
  · simp only [Category.assoc, exteriorCoefficientQuotientProjection_snd,
      exteriorIncidenceToCoefficientQuotient_parameterInclusion_assoc,
      incidenceToSupportProduct_snd_assoc, incidenceToSupportProduct_snd,
      exteriorIncidenceOriginalCoordinate_snd, exteriorIncidenceSecondCoordinate]

/-- The same original middle diagonal cuts out the complete remaining coefficient incidence. -/
theorem exteriorRemainingIncidence_originalDiagonal_isPullback :
    IsPullback
      ((A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) ≫
        correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫ pullback.fst Y.hom T.hom)
      (A.exteriorIncidenceToCoefficientQuotient B T)
      (pullback.diagonal Y.hom)
      (A.exteriorCoefficientQuotientProjection B T ≫ A.originalCoefficientMiddlePair B) := by
  simpa only [Category.assoc, exteriorCoefficientQuotientInclusion_remainingPair] using
    (A.exteriorRemainingIncidence_isPullback B T).paste_horiz
      (exteriorAmbientRemaining_isPullback X Y Z T)

end Motivic.FiniteCorrespondenceGenerator
