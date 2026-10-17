/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityParameterCommonList
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGeometry

/-! # Consumers of the identical actual parameter-kernel lists -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic RingTheory.Sequence

universe u

namespace MotivicTest.ExteriorIdentityParameterCommonList

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

example (z : A.exteriorParameterDiagonal T B) :
    ∃ t : List (A.exteriorParameterAmbientStalk B T z),
      IsRegular (A.exteriorParameterAmbientStalk B T z) t ∧
      RingHom.ker ((exteriorAmbientParameterInclusion X Y Z T).stalkMap
        (A.exteriorCoefficientQuotientInclusion B T z)).hom = Ideal.ofList t ∧
      IsRegular (((A.exteriorIdentityGenerator T).supportProduct
        (B.exteriorIdentityGenerator T)).presheaf.stalk
          (A.exteriorParameterDiagonalInclusion T B z))
        (t.map (A.exteriorParameterCoefficientStalkMap B T z).hom) ∧
      RingHom.ker ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom =
        Ideal.ofList (t.map (A.exteriorParameterCoefficientStalkMap B T z).hom) :=
  A.exteriorParameter_exists_common_regular_list B T z

end MotivicTest.ExteriorIdentityParameterCommonList
