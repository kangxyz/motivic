/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.CoefficientQuotient
public import Motivic.Aglib.AlgebraicGeometry.Simplex.ExteriorGeometry

/-! # Consumers of the full exterior coefficient parameter quotient -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityCoefficientQuotient

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom) (n : ℕ)

example :
    A.exteriorCoefficientQuotientSupport B (_root_.AlgebraicSimplex.smoothSiteObj k n) ≅
      A.exteriorParameterDiagonal (_root_.AlgebraicSimplex.smoothSiteObj k n) B :=
  A.exteriorCoefficientQuotientIso B _

example : Flat (A.exteriorCoefficientQuotientProjection B (_root_.AlgebraicSimplex.smoothSiteObj k
    n)) :=
  inferInstance

example (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    (A.exteriorCoefficientQuotientIso B T).hom ≫
      pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) =
        pullback.snd _ T.hom :=
  A.exteriorCoefficientQuotientIso_hom_parameter B T

example (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    A.exteriorCoefficientQuotientProjection B T ≫
      pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) =
        A.exteriorParameterDiagonalInclusion T B ≫
          pullback.fst
            ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
            ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
              (A.exteriorIdentitySchemeIso T).inv ≫ pullback.fst (A.projection ≫ X.hom) T.hom :=
  A.exteriorCoefficientQuotientProjection_fst B T

end MotivicTest.ExteriorIdentityCoefficientQuotient
