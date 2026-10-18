/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.ScalarLinearCombinationDifferentialCoordinates
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterBaseChange
public import Motivic.Aglib.RingTheory.Bertini.QuadraticFullSelectedPointOpen
public import Motivic.Aglib.RingTheory.Kaehler.PolynomialResidueGradient

/-! # Original selected matrices are actual scalar quadratic differential matrices -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] {σ : Type u} [Fintype σ]

/-- The actual scalar quadratic is the L-linear combination of the unchanged
original monomial functions, with the same original row and coefficient indices. -/
theorem scalarParameterFunction_eq_sum (g : σ → R) (n : ℕ)
    (c : Fin n × Exponent σ → L) (i : Fin n) :
    aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ n c i).val =
      ∑ q, c q • algebraMap R (R ⊗[k] L)
        (aeval g (parameterBasis k σ n q i).val) := by
  classical
  simp only [parameterTuple, Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  rw [← parameterBasis_map (algebraMap k L)]
  simp only [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq k L (R ⊗[k] L)]
  rw [eval₂_comp_left, ← IsScalarTower.algebraMap_eq k R (R ⊗[k] L)]

/-- The original selected derivative of a basis monomial is its actual differential. -/
theorem selectedDerivative_parameterBasis
    (x : PrimeSpectrum R) (g : σ → R) (n : ℕ)
    (q : Fin n × Exponent σ) (i : Fin n) :
    selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g
      (parameterBasis x.asIdeal.ResidueField σ n q i) =
      1 ⊗ₜ[R] D k R (aeval g (parameterBasis k σ n q i).val) := by
  change residueGeneratorGradient k R x.asIdeal.ResidueField g
    (fun j => eval (fun l => algebraMap R x.asIdeal.ResidueField (g l))
      (pderiv j (parameterBasis x.asIdeal.ResidueField σ n q i).val)) = _
  rw [← parameterBasis_map (algebraMap k x.asIdeal.ResidueField)]
  exact residueGeneratorGradient_map_polynomial k R x.asIdeal.ResidueField g _

/-- Every entry of the scalar-source cotangent matrix is the evaluation of the
actual original residue coefficient matrix, in the canonically transported basis. -/
theorem scalarQuadraticDifferential_coordinates
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    (g : σ → R) (n : ℕ)
    (B : Basis (Fin n) x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (c : Fin n × Exponent σ → L) (i j : Fin n) :
    (scalarClosedPointCotangentBasis k R L x y hy B).repr
      (1 ⊗ₜ[R ⊗[k] L] D L (R ⊗[k] L)
        (aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ n c i).val)) j =
      eval₂ (scalarClosedPointResidueMap k R L x y hy)
        (algebraMap L y.asIdeal.ResidueField ∘ c)
        (fullSelectedMatrix n B (selectedDerivative (k := k)
          (L := x.asIdeal.ResidueField) g) i j) := by
  rw [scalarParameterFunction_eq_sum, scalarClosedPointCotangentBasis_repr_D_sum]
  simp only [fullSelectedMatrix, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X,
    selectedDerivative_parameterBasis, Function.comp_apply]

end QuadraticIncidence
