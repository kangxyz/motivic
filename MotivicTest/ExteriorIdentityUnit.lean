/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorIdentityUnit

/-!
# Actual exterior identities on arbitrary smooth sources

The consumers require neither connectedness nor nonemptiness. They check the
identity on actual signed cycles, the coefficient of every diagonal component,
and the identity of every object after product with an algebraic simplex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.ExteriorIdentityUnit

variable {k : Type u} [Field k] (X T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

example :
    FiniteCorrespondence.exteriorIdentity (X := X) (Y := X) T
        (componentIdentityCycle (X := X.left) X.hom) =
      componentIdentityCycle (X := (SmoothSite.product X T).left)
        (SmoothSite.product X T).hom :=
  FiniteCorrespondence.exteriorIdentity_componentIdentityCycle T

example (a : ℤ) :
    FiniteCorrespondence.exteriorIdentity (X := X) (Y := X) T
        (a • componentIdentityCycle (X := X.left) X.hom) =
      a • componentIdentityCycle (X := (SmoothSite.product X T).left)
        (SmoothSite.product X T).hom := by
  rw [map_zsmul, FiniteCorrespondence.exteriorIdentity_componentIdentityCycle]

example (D : Set (SmoothSite.product X T).left)
    (hD : D ∈ irreducibleComponents (SmoothSite.product X T).left) :
    (FiniteCorrespondence.exteriorIdentity (X := X) (Y := X) T
      (componentIdentityCycle (X := X.left) X.hom))
        (componentIdentityGenerator (X := (SmoothSite.product X T).left)
          (SmoothSite.product X T).hom D hD) = 1 := by
  rw [FiniteCorrespondence.exteriorIdentity_componentIdentityCycle,
    componentIdentityCycle_coefficient]

example [IsEmpty X.left] :
    FiniteCorrespondence.exteriorIdentity (X := X) (Y := X) T
      (componentIdentityCycle (X := X.left) X.hom) = 0 := by
  rw [componentIdentityCycle_eq_zero_of_isEmpty, map_zero]

example (n : ℕ) (A : Cor k) :
    Cor.simplexExterior n (𝟙 A) = 𝟙 (Cor.simplexProduct A n) :=
  Cor.simplexExterior_id n A

example (n : ℕ) (A : Cor k) (a : ℤ) :
    Cor.simplexExterior n (a • 𝟙 A) = a • 𝟙 (Cor.simplexProduct A n) := by
  simp

end MotivicTest.ExteriorIdentityUnit
