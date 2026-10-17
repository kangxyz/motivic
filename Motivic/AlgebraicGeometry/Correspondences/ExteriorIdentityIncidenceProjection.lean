/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityRemainingIncidence
public import Motivic.AlgebraicGeometry.Correspondences.ExteriorPairStalks

/-!
# The Cartesian projection of the full exterior incidence

Forgetting the common identity parameter on the actual exterior incidence is
the base change of its flat coefficient-quotient projection. This preserves
the full nonreduced incidence and identifies its actual local closed fiber
with the coefficient closed fiber after the canonical point identification.
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

omit [GeometricallyIntegral T.hom] in
/-- The full original incidence is cut out by the original middle diagonal. -/
theorem originalIncidence_middle_isPullback :
    IsPullback
      (A.incidenceInclusion B ≫ correspondenceTripleMiddle X.hom Y.hom Z.hom)
      (A.incidenceToSupportProduct B) (pullback.diagonal Y.hom)
      (A.originalCoefficientMiddlePair B) :=
  (A.incidence_ambient_isPullback B).paste_horiz
    (correspondenceTriple_isPullback X.hom Y.hom Z.hom)

/-- The projection to the original incidence retains its actual middle coordinate. -/
@[reassoc]
theorem exteriorIncidenceOriginalCoordinate_middle :
    A.exteriorIncidenceOriginalCoordinate B T ≫ A.incidenceInclusion B ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom =
      (A.exteriorIdentityGenerator T).incidenceInclusion (B.exteriorIdentityGenerator T) ≫
        correspondenceTripleMiddle (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫
            pullback.fst Y.hom T.hom := by
  simp only [correspondenceTripleMiddle, Category.assoc, incidenceInclusion_fst_assoc]
  change A.exteriorIncidenceOriginalCoordinate B T ≫ A.incidenceFst B ≫ A.targetProjection =
    (A.exteriorIdentityGenerator T).incidenceFst (B.exteriorIdentityGenerator T) ≫
      (A.exteriorIdentityGenerator T).targetProjection ≫ pullback.fst Y.hom T.hom
  simp only [exteriorIncidenceOriginalCoordinate_fst_assoc, Category.assoc,
    exteriorIdentitySchemeIso_inv_old_target]

/-- The full exterior incidence is the Cartesian inverse image of the original incidence. -/
theorem exteriorIncidenceProjection_isPullback :
    IsPullback (A.exteriorIncidenceOriginalCoordinate B T)
      (A.exteriorIncidenceToCoefficientQuotient B T) (A.incidenceToSupportProduct B)
      (A.exteriorCoefficientQuotientProjection B T) := by
  apply IsPullback.of_right (t := A.originalIncidence_middle_isPullback B)
  · simpa only [Category.assoc, exteriorIncidenceOriginalCoordinate_middle] using
      A.exteriorRemainingIncidence_originalDiagonal_isPullback B T
  · exact (A.exteriorIncidenceToCoefficientQuotient_projection B T).symm

instance exteriorIncidenceOriginalCoordinate_flat :
    Flat (A.exteriorIncidenceOriginalCoordinate B T) :=
  MorphismProperty.of_isPullback (A.exteriorIncidenceProjection_isPullback B T).flip
    (inferInstanceAs (Flat (A.exteriorCoefficientQuotientProjection B T)))

/-- The genuine coefficient and incidence local closed fibers have the same length. -/
theorem exteriorIncidenceProjection_closedFiber_length
    (w : (A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)) :
    Module.length ((A.exteriorParameterDiagonal T B).presheaf.stalk
        (A.exteriorIncidenceToCoefficientQuotient B T w))
      (Koszul.coefficientClosedFiber (Diagonal.baseChangeStalkMap
        (A.exteriorIncidenceProjection_isPullback B T) w).hom) =
    Module.length
      (((A.exteriorIdentityGenerator T).incidence (B.exteriorIdentityGenerator T)).presheaf.stalk w)
      (Koszul.coefficientClosedFiber
        ((A.exteriorIncidenceOriginalCoordinate B T).stalkMap w).hom) :=
  Intersection.exteriorClosedFiber_length (A.exteriorIncidenceOriginalCoordinate B T)
    (A.exteriorIncidenceToCoefficientQuotient B T) (A.incidenceToSupportProduct B)
    (A.exteriorCoefficientQuotientProjection B T) (A.exteriorIncidenceProjection_isPullback B T) w

end Motivic.FiniteCorrespondenceGenerator
