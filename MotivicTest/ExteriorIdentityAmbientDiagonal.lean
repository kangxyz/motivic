/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityAmbientDiagonal
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-! # The actual simplex exterior ambient has two Cartesian diagonal blocks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityAmbientDiagonal

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))

example : Flat (exteriorAmbientRemainingPair X Y Z T) := inferInstance

example :
    exteriorAmbientRemainingInclusion X Y Z T ≫ exteriorAmbientParameterInclusion X Y Z T =
      correspondenceTripleInclusion (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom :=
  exteriorAmbientRemainingInclusion_parameterInclusion X Y Z T

example :
    IsPullback
      (correspondenceTripleMiddle (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom ≫ pullback.fst Y.hom T.hom)
      (exteriorAmbientRemainingInclusion X Y Z T)
      (pullback.diagonal Y.hom) (exteriorAmbientRemainingPair X Y Z T) :=
  exteriorAmbientRemaining_isPullback X Y Z T

example (n : ℕ) :
    Flat (exteriorAmbientRemainingPair X Y Z (AlgebraicSimplex.smoothSiteObj k n)) :=
  inferInstance

example (z : exteriorAmbientParameterQuotient X Y Z T) :
    ∃ t : List ((correspondenceIntersectionAmbient (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).presheaf.stalk
          (exteriorAmbientParameterInclusion X Y Z T z)),
      RingTheory.Sequence.IsRegular
        ((correspondenceIntersectionAmbient (SmoothSite.product X T).hom
          (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom).presheaf.stalk
            (exteriorAmbientParameterInclusion X Y Z T z)) t ∧
        RingHom.ker ((exteriorAmbientParameterInclusion X Y Z T).stalkMap z).hom =
          Ideal.ofList t :=
  exteriorAmbientParameter_exists_regular_kernel X Y Z T z

end MotivicTest.ExteriorIdentityAmbientDiagonal
