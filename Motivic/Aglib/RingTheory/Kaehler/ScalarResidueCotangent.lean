/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Cotangent vectors at an actual scalar-extended affine point

The tensor algebra is literally `R ⊗[k] L`, and both differentials use its
canonical original-ring map. No residue-field section is selected.
-/

@[expose] public noncomputable section

open TensorProduct
open scoped TensorProduct

namespace KaehlerDifferential

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k R L K : Type u) [CommRing k] [CommRing R] [CommRing L] [CommRing K]
  [Algebra k R] [Algebra k L] [Algebra (R ⊗[k] L) K]
  [Algebra R K] [IsScalarTower R (R ⊗[k] L) K]

/-- Canonical residue-cotangent base change on the actual scalar tensor algebra. -/
def scalarResidueEquiv :
    K ⊗[R] Ω[R⁄k] ≃ₗ[K] K ⊗[R ⊗[k] L] Ω[(R ⊗[k] L)⁄L] :=
  (AlgebraTensorModule.cancelBaseChange R (R ⊗[k] L) K K Ω[R⁄k]).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl K K)
      (tensorKaehlerEquiv k L R (R ⊗[k] L))

/-- Every original differential is carried to its literal scalar-extended function. -/
theorem scalarResidueEquiv_tmul_D (a : K) (r : R) :
    scalarResidueEquiv k R L K (a ⊗ₜ[R] D k R r) =
      a ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L) (algebraMap R (R ⊗[k] L) r) := by
  simp [scalarResidueEquiv, tensorKaehlerEquiv_tmul_D]

end KaehlerDifferential
