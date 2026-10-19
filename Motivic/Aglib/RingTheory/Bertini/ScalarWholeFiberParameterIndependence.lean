/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.SelectedMinorFieldExtension
public import Motivic.Aglib.RingTheory.Bertini.QuadraticDiagonalFieldExtension
public import Motivic.Aglib.RingTheory.Bertini.MovingPointScalarBadPointExclusion
public import Motivic.Aglib.RingTheory.Polynomial.Residue.FiberEvaluation

/-! # The same scalar tuple is independent at every original coefficient-algebra point -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

/-- Both the diagonal and off-diagonal cases use the actual original coefficient
algebra and the same L-valued parameters. No infinite-field hypothesis is used. -/
theorem independent_scalarTuple_at_original_coefficient_point
    (k R L K : Type u) [Field k] [CommRing R] [Field L] [Field K]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L] [Algebra k K]
    [Algebra L K] [IsScalarTower k L K] [Algebra R K]
    (x : PrimeSpectrum R)
    [Algebra (ClosedPoint.CoefficientRing k R x) K]
    [IsScalarTower k (ClosedPoint.CoefficientRing k R x) K]
    [IsScalarTower R (ClosedPoint.CoefficientRing k R x) K]
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
    (hv : ∀ i, eval (fun j => algebraMap R K (g j))
        (parameterTuple K σ d (algebraMap L K ∘ c) i).val =
      eval (fun j => algebraMap (ClosedPoint.CoefficientRing k R x) K
        (ClosedPoint.selectedValue k R x (g j)))
        (parameterTuple K σ d (algebraMap L K ∘ c) i).val) :
    LinearIndependent K (fun i => residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l))
        (pderiv j (parameterTuple K σ d (algebraMap L K ∘ c) i).val))) := by
  by_cases he : (fun j => algebraMap R K (g j)) =
      fun j => algebraMap (ClosedPoint.CoefficientRing k R x) K
        (ClosedPoint.selectedValue k R x (g j))
  · let : Algebra x.asIdeal.ResidueField K :=
      (ClosedPoint.residueFieldMap k R x K).toRingHom.toAlgebra
    let : IsScalarTower R x.asIdeal.ResidueField K :=
      ClosedPoint.diagonal_scalarTower k R x K σ g hg (fun j => congrFun he j)
    let : IsScalarTower k x.asIdeal.ResidueField K :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (ClosedPoint.residueFieldMap k R x K).commutes r |>.symm
    let : IsScalarTower k R K := IsScalarTower.to₁₂₄ k R x.asIdeal.ResidueField K
    exact independent_selectedDerivative_of_eval₂_minor k R x.asIdeal.ResidueField K
      g d B (algebraMap L K ∘ c)
      (eval₂_ne_zero_of_isUnit_residueFiber k x.asIdeal.ResidueField L K _ c hu)
  · have hfK : eval₂ (algebraMap k K) (algebraMap L K ∘ c) f ≠ 0 := by
      rw [IsScalarTower.algebraMap_eq k L K, ← eval₂_comp_left]
      simpa only [map_zero] using (algebraMap L K).injective.ne hf
    exact MovingPointChart.linearIndependent_of_eval₂_parameter_relation_ne_zero
      k R (ClosedPoint.CoefficientRing k R x) K g
      (fun j => ClosedPoint.selectedValue k R x (g j)) d f (algebraMap L K ∘ c)
      hfK hz (parameterTuple K σ d (algebraMap L K ∘ c))
      (parameterTuple_repr K σ d (algebraMap L K ∘ c)) he hv

end QuadraticIncidence
