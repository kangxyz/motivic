/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.PrescribedTrivialization
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Consumers retaining a specified coordinate on the whole closed boundary -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Motivic.MotivicTest.PrescribedTrivialization

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]

/-- The full defining ideal survives: neither radicalization nor choosing a
new boundary coordinate is permitted in this consumer. -/
theorem wholeBoundaryCoordinate
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1)
    (I : Ideal R) (e : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] R ⧸ I) :
    ∃ (r : R) (hr : algebraMap R (R ⧸ I) r = 1),
      r - 1 ∈ I ∧
      PrimeSpectrum.zeroLocus (I : Set R) ⊆ PrimeSpectrum.basicOpen r ∧
      ∃ (d : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r),
        ∀ m : M,
          IsLocalization.Away.lift r (hr ▸ isUnit_one)
              (d (LocalizedModule.mkLinearMap (Submonoid.powers r) M m)) =
            e (1 ⊗ₜ[R] m) :=
  Module.exists_prescribed_principal_coordinate_quotient hRank I e

/-- A prescribed, possibly nonconstant boundary unit is extended as a
coordinate, not assumed to have an invertible global lift. This works for
any ideal in any nontrivial commutative ring. -/
theorem prescribedBoundaryUnit [Nontrivial R] (I : Ideal R) (u : (R ⧸ I)ˣ) :
    ∃ (r : R) (hr : algebraMap R (R ⧸ I) r = 1),
      r - 1 ∈ I ∧
      PrimeSpectrum.zeroLocus (I : Set R) ⊆ PrimeSpectrum.basicOpen r ∧
      ∃ (d : LocalizedModule.Away r R ≃ₗ[Localization.Away r] Localization.Away r),
        ∀ x : R,
          IsLocalization.Away.lift r (hr ▸ isUnit_one)
              (d (LocalizedModule.mkLinearMap (Submonoid.powers r) R x)) =
            (u : R ⧸ I) * algebraMap R (R ⧸ I) x := by
  let e : (R ⧸ I) ⊗[R] R ≃ₗ[R ⧸ I] R ⧸ I :=
    TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I) ≪≫ₗ LinearEquiv.smulOfUnit u
  obtain ⟨r, hr, hi, hp, d, hd⟩ := wholeBoundaryCoordinate
    (M := R) (fun p ↦ by simp [Module.rankAtStalk_eq_finrank_of_free]) I e
  refine ⟨r, hr, hi, hp, d, fun x ↦ ?_⟩
  simpa [e, LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv,
    Algebra.smul_def, Units.smul_def] using hd x

set_option linter.hashCommand false in
#print axioms Module.exists_prescribed_principal_coordinate
set_option linter.hashCommand false in
#print axioms Module.exists_prescribed_principal_coordinate_quotient
set_option linter.hashCommand false in
#print axioms prescribedBoundaryUnit

end Motivic.MotivicTest.PrescribedTrivialization
