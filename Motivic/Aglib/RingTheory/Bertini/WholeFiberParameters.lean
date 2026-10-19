/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticDiagonalFieldExtension
public import Motivic.Aglib.RingTheory.Bertini.WholeOffDiagonalFiberParameters
public import Motivic.Aglib.RingTheory.Kaehler.PolynomialResidueGradient

/-! # One original quadratic tuple controls all field-valued points of the selected fiber -/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial QuadraticIncidence
universe u
namespace QuadraticIncidence

/-- Both alternatives use the same actual closed-point coefficient algebra and coefficients.
The diagonal alternative is valid over every extension field, not only at the residue field. -/
theorem exists_parameterTuple_whole_fiber_independent (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K]
        [Algebra (ClosedPoint.CoefficientRing k R p) K]
        [IsScalarTower k (ClosedPoint.CoefficientRing k R p) K]
        [IsScalarTower R (ClosedPoint.CoefficientRing k R p) K],
        (∀ i, eval (fun j => algebraMap R K (g j))
            (parameterTuple K σ d (algebraMap k K ∘ c) i).val =
          eval (fun j => algebraMap (ClosedPoint.CoefficientRing k R p) K
            (ClosedPoint.selectedValue k R p (g j)))
            (parameterTuple K σ d (algebraMap k K ∘ c) i).val) →
        LinearIndependent K (fun i => residueGeneratorGradient k R K g
          (fun j => eval (fun l => algebraMap R K (g l))
            (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
  obtain ⟨q₀, hq₀, hselected⟩ := exists_selectedPoint_open_of_smooth
    (L := p.asIdeal.ResidueField) g hg d hd
  obtain ⟨c, hc, hoff⟩ := exists_goodOffDiagonalParameters k R
    (ClosedPoint.CoefficientRing k R p) g hg
    (fun j => ClosedPoint.selectedValue k R p (g j)) d hd (q₀ * q) (mul_ne_zero hq₀ hq)
  have hc₀ : eval c q₀ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hc)).1
  have hcq : eval c q ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hc)).2
  refine ⟨c, hcq, ?_⟩
  intro K _ _ _ _ _ _ hvalue
  by_cases he : (fun j => algebraMap R K (g j)) =
      fun j => algebraMap (ClosedPoint.CoefficientRing k R p) K
        (ClosedPoint.selectedValue k R p (g j))
  · exact ClosedPoint.independent_parameterTuple_at_diagonal k R p K g hg d c
      (hselected c hc₀) (fun j => congrFun he j)
  · exact hoff K he hvalue

end QuadraticIncidence
