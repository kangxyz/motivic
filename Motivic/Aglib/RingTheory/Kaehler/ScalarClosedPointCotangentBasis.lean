/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.ScalarResidueCotangent
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Original residue bases at the actual scalar-extended closed point -/

@[expose] public noncomputable section

open Module TensorProduct
open scoped TensorProduct

namespace KaehlerDifferential

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L]
  (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
  (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)

/-- The residue map is the canonical map of the literal original prime preimage. -/
def scalarClosedPointResidueMap : x.asIdeal.ResidueField →+* y.asIdeal.ResidueField :=
  Ideal.ResidueField.map x.asIdeal y.asIdeal (algebraMap R (R ⊗[k] L))
    (congrArg PrimeSpectrum.asIdeal hy).symm

/-- The residue-field tower follows from the actual closed-fiber equation. -/
theorem scalarClosedPointResidueTower :
    let : Algebra x.asIdeal.ResidueField y.asIdeal.ResidueField :=
      (scalarClosedPointResidueMap k R L x y hy).toAlgebra
    IsScalarTower R x.asIdeal.ResidueField y.asIdeal.ResidueField := by
  let : Algebra x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    (scalarClosedPointResidueMap k R L x y hy).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (IsScalarTower.algebraMap_apply R (R ⊗[k] L) y.asIdeal.ResidueField r).trans
    (Ideal.ResidueField.map_algebraMap x.asIdeal y.asIdeal
      (algebraMap R (R ⊗[k] L)) (congrArg PrimeSpectrum.asIdeal hy).symm r).symm

/-- A basis at the original mark gives a basis of the actual new cotangent fiber,
using the canonical residue map and the literal scalar-source differential. -/
def scalarClosedPointCotangentBasis {ι : Type v}
    (B : Basis ι x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k])) :
    Basis ι y.asIdeal.ResidueField
      (y.asIdeal.ResidueField ⊗[R ⊗[k] L] Ω[(R ⊗[k] L)⁄L]) := by
  let : Algebra x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    (scalarClosedPointResidueMap k R L x y hy).toAlgebra
  let : IsScalarTower R x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    scalarClosedPointResidueTower k R L x y hy
  exact (B.baseChange y.asIdeal.ResidueField).map
    ((AlgebraTensorModule.cancelBaseChange R x.asIdeal.ResidueField
      y.asIdeal.ResidueField y.asIdeal.ResidueField Ω[R⁄k]) ≪≫ₗ
        scalarResidueEquiv k R L y.asIdeal.ResidueField)

end KaehlerDifferential
