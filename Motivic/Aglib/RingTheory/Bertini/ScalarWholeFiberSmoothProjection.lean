/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.ScalarWholeFiberDifferentialIndependence
public import Motivic.Aglib.RingTheory.FiniteScalarExtensionTrdeg

/-! # Actual scalar quadratic projection is smooth along its whole selected fiber -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential MvPolynomial AlgebraicGeometry
open scoped TensorProduct

namespace QuadraticIncidence

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Original bad-chart equations and the full minor-fiber unit produce genuine
smooth relative-curve neighborhoods at every prime of the same scalar fiber.
No smoothness conclusion or scalar transcendence degree is supplied. -/
theorem exists_scalar_wholeFiber_smooth_projection
    (k R L : Type u) [Field k] [CommRing R] [IsDomain R] [Field L]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L] [Module.Finite k L]
    [IsDomain (R ⊗[k] L)]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (B : Basis (Fin (d + 1)) x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (f : MvPolynomial (Fin d × Exponent σ) k) (c : Fin d × Exponent σ → L)
    (hf : eval₂ (algebraMap k L) c f ≠ 0)
    (hz : ∀ (i₀ : Fin d) (j : σ),
      MovingPointChart.chartParameterMap k R (ClosedPoint.CoefficientRing k R x) g
        (fun j => ClosedPoint.selectedValue k R x (g j)) d i₀ j f = 0)
    (hu : let : Algebra (MvPolynomial (Fin d × Exponent σ) k) L :=
        (eval₂Hom (algebraMap k L) c).toAlgebra
      IsUnit (1 ⊗ₜ[MvPolynomial (Fin d × Exponent σ) k]
        (residueCoefficientEquiv k x.asIdeal.ResidueField _).symm
          (selectedDeterminant d B
            (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g)) :
        L ⊗[MvPolynomial (Fin d × Exponent σ) k]
          (MvPolynomial (Fin d × Exponent σ) k ⊗[k] x.asIdeal.ResidueField)))
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (Q : PrimeSpectrum (R ⊗[k] L))
    (hQ : Ideal.comap (aeval (R := L) (fun i =>
        aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val)).toRingHom
        y.asIdeal =
      Ideal.comap (aeval (R := L) (fun i =>
        aeval (algebraMap R (R ⊗[k] L) ∘ g) (parameterTuple L σ d c i).val)).toRingHom
        Q.asIdeal) :
    ∃ s ∉ Q.asIdeal, SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (R ⊗[k] L) (Localization.Away s)).comp
          (aeval (R := L) (fun i => aeval (algebraMap R (R ⊗[k] L) ∘ g)
            (parameterTuple L σ d c i).val)).toRingHom))) := by
  let : Algebra.Smooth L (R ⊗[k] L) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)
  apply exists_smooth_one_of_residue_independent L (R ⊗[k] L) Q.asIdeal d _
  · exact (Algebra.TensorProduct.trdeg_right_eq_of_finite k R L).trans hd
  · exact independent_scalar_differentials_of_same_fiber k R L x y hy
      g hg d B f c hf hz hu Q hQ

end QuadraticIncidence
