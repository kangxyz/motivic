/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentBasis

/-! # Actual differential coordinates in the transported closed-point basis -/

@[expose] public noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace KaehlerDifferential

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Coordinates of every original function differential are transported by the
canonical residue-field map, in the actual scalar-source cotangent basis. -/
theorem scalarClosedPointCotangentBasis_repr_D
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {ι : Type v}
    (B : Basis ι x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (r : R) (i : ι) :
    (scalarClosedPointCotangentBasis k R L x y hy B).repr
      (1 ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L) (algebraMap R (R ⊗[k] L) r)) i =
      scalarClosedPointResidueMap k R L x y hy
        (B.repr (1 ⊗ₜ[R] D k R r) i) := by
  let : Algebra x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    (scalarClosedPointResidueMap k R L x y hy).toAlgebra
  let : IsScalarTower R x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    scalarClosedPointResidueTower k R L x y hy
  rw [← scalarResidueEquiv_tmul_D k R L y.asIdeal.ResidueField]
  simp [scalarClosedPointCotangentBasis, Basis.map, Algebra.smul_def]
  rfl

end KaehlerDifferential
