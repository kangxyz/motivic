/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityIncidenceProjection
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-! # Consumers of the actual Cartesian exterior-incidence projection -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityIncidenceProjection

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

example :
    IsPullback (A.exteriorIncidenceOriginalCoordinate B T)
      (A.exteriorIncidenceToCoefficientQuotient B T) (A.incidenceToSupportProduct B)
      (A.exteriorCoefficientQuotientProjection B T) :=
  A.exteriorIncidenceProjection_isPullback B T

example : Flat (A.exteriorIncidenceOriginalCoordinate B T) := inferInstance

example (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) :
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk
        (A.exteriorIncidenceToCoefficientQuotient B T w))
      (Koszul.coefficientClosedFiber (Diagonal.baseChangeStalkMap
        (A.exteriorIncidenceProjection_isPullback B T) w).hom) =
    Module.length
      (((A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)).presheaf.stalk w)
      (Koszul.coefficientClosedFiber
        ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap w).hom) :=
  A.exteriorIncidenceProjection_closedFiber_length B T w

omit [GeometricallyIntegral T.hom] in
example (n : ℕ) :
    Flat (A.exteriorIncidenceOriginalCoordinate B (AlgebraicSimplex.smoothSiteObj k n)) :=
  inferInstance

end MotivicTest.ExteriorIdentityIncidenceProjection
