/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentCoordinates

/-! # Coordinates of actual scalar linear combinations of original functions -/

@[expose] public noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace KaehlerDifferential

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Scalar coefficients act on the actual new function, and the original
residue coordinates are transported by the canonical residue-field map. -/
theorem scalarClosedPointCotangentBasis_repr_D_sum
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {ι : Type v} {τ : Type u} [Fintype τ]
    (B : Basis ι x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (c : τ → L) (t : τ → R) (i : ι) :
    (scalarClosedPointCotangentBasis k R L x y hy B).repr
      (1 ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L)
        (∑ q, c q • algebraMap R (R ⊗[k] L) (t q))) i =
      ∑ q, scalarClosedPointResidueMap k R L x y hy
        (B.repr (1 ⊗ₜ[R] D k R (t q)) i) * algebraMap L y.asIdeal.ResidueField (c q) := by
  classical
  let S := R ⊗[k] L
  let K := y.asIdeal.ResidueField
  let B' := scalarClosedPointCotangentBasis k R L x y hy B
  let ℓ : S →ₗ[L] (ι →₀ K) :=
    (B'.repr.toLinearMap.restrictScalars L).comp
      ((((TensorProduct.mk S K Ω[S⁄L]) 1).restrictScalars L).comp
        (D L S).toLinearMap)
  change ℓ (∑ q, c q • algebraMap R S (t q)) i = _
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Algebra.smul_def]
  change algebraMap L K (c q) * B'.repr
      (1 ⊗ₜ[S] D L S (algebraMap R S (t q))) i = _
  rw [scalarClosedPointCotangentBasis_repr_D]
  exact mul_comm _ _

end KaehlerDifferential
