/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityAmbientDiagonal

/-!
# The coefficient quotient in the actual exterior ambient

The literal parameter quotient of the support product is the Cartesian
inverse image of the ambient parameter quotient. Its remaining original
middle coordinates are exactly the previously constructed flat projection
onto the original coefficient scheme followed by the original middle pair.
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

@[reassoc]
theorem exteriorIdentityParameter_target :
    A.exteriorIdentityParameter T =
      (A.exteriorIdentityGenerator T).targetProjection ≫ pullback.snd Y.hom T.hom := by
  rw [← A.exteriorIdentitySchemeIso_inv_target T]
  simp only [Category.assoc, exteriorIdentityTarget_snd]

@[reassoc]
theorem exteriorIdentityParameter_source :
    A.exteriorIdentityParameter T =
      (A.exteriorIdentityGenerator T).projection ≫ pullback.snd X.hom T.hom := by
  rw [← A.exteriorIdentitySchemeIso_inv_source T]
  simp only [Category.assoc, exteriorIdentitySource_snd]

/-- The actual coefficient parameter pair is induced by the ambient parameter pair. -/
@[reassoc]
theorem exteriorCoefficientParameterPair_ambient :
    (A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T) ≫
      exteriorAmbientParameterPair X Y Z T = A.exteriorCoefficientParameterPair T B := by
  apply pullback.hom_ext
  · simp only [exteriorAmbientParameterPair, ProductDiagonal.parameterPair,
      ← SmoothSite.product_hom Y T, pullback.map,
      Category.assoc, pullback.lift_fst, correspondenceMiddlePair_fst_assoc,
      supportProductInclusion_fst_assoc, exteriorCoefficientParameterPair_fst,
      exteriorIdentityParameter_target]
  · simp only [exteriorAmbientParameterPair, ProductDiagonal.parameterPair,
      ← SmoothSite.product_hom Y T, pullback.map,
      Category.assoc, pullback.lift_snd, correspondenceMiddlePair_snd_assoc,
      supportProductInclusion_snd_assoc, exteriorCoefficientParameterPair_snd,
      exteriorIdentityParameter_source]
    rfl

/-- The actual coefficient inclusion after imposing the parameter diagonal. -/
def exteriorCoefficientQuotientInclusion : A.exteriorParameterDiagonal T B ⟶
    exteriorAmbientParameterQuotient X Y Z T :=
  pullback.lift
    (pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B))
    (A.exteriorParameterDiagonalInclusion T B ≫
      (A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T))
    (by
      rw [Category.assoc, A.exteriorCoefficientParameterPair_ambient B T]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem exteriorCoefficientQuotientInclusion_parameter :
    A.exteriorCoefficientQuotientInclusion B T ≫
      pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T) =
        pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorCoefficientQuotientInclusion_ambient :
    A.exteriorCoefficientQuotientInclusion B T ≫ exteriorAmbientParameterInclusion X Y Z T =
      A.exteriorParameterDiagonalInclusion T B ≫
        (A.exteriorIdentityGenerator T).supportProductInclusion (B.exteriorIdentityGenerator T) :=
  pullback.lift_snd _ _ _

/-- The two parameter quotients form the literal Cartesian coefficient square. -/
theorem exteriorCoefficientQuotientInclusion_isPullback :
    IsPullback (A.exteriorCoefficientQuotientInclusion B T)
      (A.exteriorParameterDiagonalInclusion T B)
      (exteriorAmbientParameterInclusion X Y Z T)
      ((A.exteriorIdentityGenerator T).supportProductInclusion
        (B.exteriorIdentityGenerator T)) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst (pullback.diagonal T.hom) (exteriorAmbientParameterPair X Y Z T))
    (h₂₂ := exteriorAmbientParameterPair X Y Z T)
  · simpa only [exteriorCoefficientQuotientInclusion_parameter,
      exteriorCoefficientParameterPair_ambient] using A.exteriorParameterDiagonal_isPullback T B
  · exact A.exteriorCoefficientQuotientInclusion_ambient B T
  · exact exteriorAmbientParameter_isPullback X Y Z T

instance exteriorCoefficientQuotientInclusion_isClosedImmersion :
    IsClosedImmersion (A.exteriorCoefficientQuotientInclusion B T) :=
  MorphismProperty.of_isPullback (A.exteriorCoefficientQuotientInclusion_isPullback B T).flip
    inferInstance

/-- The remaining ambient pair and the original coefficient pair agree literally. -/
@[reassoc]
theorem exteriorCoefficientQuotientInclusion_remainingPair :
    A.exteriorCoefficientQuotientInclusion B T ≫ exteriorAmbientRemainingPair X Y Z T =
      A.exteriorCoefficientQuotientProjection B T ≫ A.originalCoefficientMiddlePair B := by
  rw [A.exteriorCoefficientQuotientProjection_middlePair B T]
  apply pullback.hom_ext
  · simp only [exteriorAmbientRemainingPair, Category.assoc,
      ProductDiagonalBaseChange.remainingMap_fst,
      ← SmoothSite.product_hom Y T, exteriorCoefficientQuotientInclusion_ambient_assoc,
      correspondenceMiddlePair_fst_assoc, supportProductInclusion_fst_assoc,
      exteriorCoefficientOldMiddlePair_fst]
  · simp only [exteriorAmbientRemainingPair, Category.assoc,
      ProductDiagonalBaseChange.remainingMap_snd,
      ← SmoothSite.product_hom Y T, exteriorCoefficientQuotientInclusion_ambient_assoc,
      correspondenceMiddlePair_snd_assoc, supportProductInclusion_snd_assoc,
      exteriorCoefficientOldMiddlePair_snd]
    rfl

end Motivic.FiniteCorrespondenceGenerator
