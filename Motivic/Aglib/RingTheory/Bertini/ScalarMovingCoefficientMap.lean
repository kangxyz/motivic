/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.ClosedPointMovingCoefficients
public import Motivic.Aglib.RingTheory.Kaehler.ScalarClosedPointCotangentBasis

/-! # Restrict scalar moving points to the literal original coefficient algebra -/

@[expose] public noncomputable section

open KaehlerDifferential
open scoped TensorProduct

namespace QuadraticIncidence.ClosedPoint

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L]
  (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
  (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)

/-- The canonical residue map is compatible with the original ground field. -/
def scalarResidueAlgHom : x.asIdeal.ResidueField →ₐ[k] y.asIdeal.ResidueField := by
  let : Algebra x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    (scalarClosedPointResidueMap k R L x y hy).toAlgebra
  let : IsScalarTower R x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    scalarClosedPointResidueTower k R L x y hy
  let : IsScalarTower k x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    IsScalarTower.to₁₃₄ k R x.asIdeal.ResidueField y.asIdeal.ResidueField
  exact IsScalarTower.toAlgHom k x.asIdeal.ResidueField y.asIdeal.ResidueField

/-- Both tensor factors are the actual moving source and actual marked residue
field. This map neither chooses a rational lift nor replaces the closed fiber. -/
def scalarCoefficientMap : CoefficientRing k R x →ₐ[k]
    CoefficientRing L (R ⊗[k] L) y :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom k R (CoefficientRing L (R ⊗[k] L) y))
    (((Algebra.TensorProduct.includeRight : y.asIdeal.ResidueField →ₐ[L]
      CoefficientRing L (R ⊗[k] L) y).restrictScalars k).comp
        (scalarResidueAlgHom k R L x y hy)) (fun _ _ => Commute.all _ _)

/-- The moving copy of every original function is unchanged. -/
theorem scalarCoefficientMap_algebraMap (r : R) :
    scalarCoefficientMap k R L x y hy (algebraMap R (CoefficientRing k R x) r) =
      algebraMap R (CoefficientRing L (R ⊗[k] L) y) r := by
  simp [scalarCoefficientMap, Algebra.TensorProduct.algebraMap_apply]

/-- The selected copy is the residue of the same scalar-extended function. -/
theorem scalarCoefficientMap_selectedValue (r : R) :
    scalarCoefficientMap k R L x y hy (selectedValue k R x r) =
      selectedValue L (R ⊗[k] L) y (algebraMap R (R ⊗[k] L) r) := by
  have hr : scalarResidueAlgHom k R L x y hy
      (algebraMap R x.asIdeal.ResidueField r) =
        algebraMap (R ⊗[k] L) y.asIdeal.ResidueField
          (algebraMap R (R ⊗[k] L) r) :=
    Ideal.ResidueField.map_algebraMap x.asIdeal y.asIdeal
      (algebraMap R (R ⊗[k] L)) (congrArg PrimeSpectrum.asIdeal hy).symm r
  simpa [scalarCoefficientMap, selectedValue, ← Algebra.TensorProduct.one_def] using
    congrArg (fun a : y.asIdeal.ResidueField => (1 : R ⊗[k] L) ⊗ₜ[L] a) hr

end QuadraticIncidence.ClosedPoint
