/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityRemainingPair
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-! # Consumers of the actual surviving middle equations and all-degree lengths -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityRemainingPair

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

example :
    A.exteriorCoefficientQuotientProjection B T ≫ A.originalCoefficientMiddlePair B =
      A.exteriorParameterDiagonalInclusion T B ≫ A.exteriorCoefficientOldMiddlePair B T :=
  A.exteriorCoefficientQuotientProjection_middlePair B T

example (z : A.exteriorParameterDiagonal T B)
    (p : (pullback Y.hom Y.hom : Scheme))
    (hp : p = A.originalCoefficientMiddlePair B
      (A.exteriorCoefficientQuotientProjection B T z))
    (hp' : p = A.exteriorCoefficientOldMiddlePair B T
      (A.exteriorParameterDiagonalInclusion T B z))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk p)) (n : ℕ) :
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
      ((Koszul.coefficientComplex
        (ModuleCat.of ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
          ((A.exteriorParameterDiagonal T B).presheaf.stalk z))
        ((s.map (StalkTransport.pointedMap (A.exteriorCoefficientOldMiddlePair B T)
          (A.exteriorParameterDiagonalInclusion T B z) p hp').hom).map
            ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom)).homology n) =
    Module.length ((A.supportProduct B).presheaf.stalk
        (A.exteriorCoefficientQuotientProjection B T z))
      ((Koszul.coefficientComplex
        (ModuleCat.of ((A.supportProduct B).presheaf.stalk
            (A.exteriorCoefficientQuotientProjection B T z))
          ((A.supportProduct B).presheaf.stalk
            (A.exteriorCoefficientQuotientProjection B T z)))
        (s.map (StalkTransport.pointedMap (A.originalCoefficientMiddlePair B)
          (A.exteriorCoefficientQuotientProjection B T z) p hp).hom)).homology n) *
      Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
        (Koszul.coefficientClosedFiber
          ((A.exteriorCoefficientQuotientProjection B T).stalkMap z).hom) :=
  A.exteriorRemainingPair_homology_length B T z p hp hp' s n

omit [GeometricallyIntegral T.hom] in
example (n : ℕ) :
    A.exteriorCoefficientQuotientProjection B (AlgebraicSimplex.smoothSiteObj k n) ≫
        A.originalCoefficientMiddlePair B =
      A.exteriorParameterDiagonalInclusion (AlgebraicSimplex.smoothSiteObj k n) B ≫
        A.exteriorCoefficientOldMiddlePair B (AlgebraicSimplex.smoothSiteObj k n) :=
  A.exteriorCoefficientQuotientProjection_middlePair B _

end MotivicTest.ExteriorIdentityRemainingPair
