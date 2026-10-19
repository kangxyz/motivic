/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticEtaleCriterion
public import Motivic.Aglib.RingTheory.Polynomial.Residue.FiberEvaluation

/-! # Entire original determinant fibers produce actual scalar étale neighborhoods -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual determinant unit supplied by simultaneous finite-field avoidance
produces an étale neighborhood at every point over the original marked prime.
The residue map and differential coordinates are constructed internally. -/
theorem exists_scalar_quadratic_etale_of_isUnit_original_fiber
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L] [Algebra.Smooth L (R ⊗[k] L)]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {σ : Type u} [Fintype σ] (g : σ → R) (n : ℕ)
    (B : Basis (Fin n) x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (c : Fin n × Exponent σ → L)
    (hu : let : Algebra (MvPolynomial (Fin n × Exponent σ) k) L :=
        (eval₂Hom (algebraMap k L) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial (Fin n × Exponent σ) k]
        (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
          (fullSelectedDeterminant n B
            (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)) :
        L ⊗[MvPolynomial (Fin n × Exponent σ) k]
          (MvPolynomial (Fin n × Exponent σ) k ⊗[k] x.asIdeal.ResidueField))) :
    ∃ r ∉ y.asIdeal, ((algebraMap (R ⊗[k] L) (Localization.Away r)).comp
      (aeval (R := L) (fun i => aeval (algebraMap R (R ⊗[k] L) ∘ g)
        (parameterTuple L σ n c i).val)).toRingHom).Etale := by
  let : Algebra x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    (scalarClosedPointResidueMap k R L x y hy).toAlgebra
  let : IsScalarTower R x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    scalarClosedPointResidueTower k R L x y hy
  let : IsScalarTower k x.asIdeal.ResidueField y.asIdeal.ResidueField :=
    IsScalarTower.to₁₃₄ k R x.asIdeal.ResidueField y.asIdeal.ResidueField
  apply exists_scalar_quadratic_etale_of_original_determinant k R L x y hy g n B c
  exact eval₂_ne_zero_of_isUnit_residueFiber k x.asIdeal.ResidueField L
    y.asIdeal.ResidueField _ c hu

end QuadraticIncidence
