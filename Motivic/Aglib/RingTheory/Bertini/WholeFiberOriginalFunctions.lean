/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberParameters
public import Motivic.Aglib.RingTheory.Kaehler.PolynomialResidueGradient

/-! # One original quadratic tuple controls all field-valued points of the selected fiber -/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial QuadraticIncidence
universe u
namespace QuadraticIncidence

/-- Both alternatives use the same actual closed-point coefficient algebra and coefficients.
The diagonal alternative is valid over every extension field, not only at the residue field. -/
theorem exists_originalFunctions_whole_fiber_independent (k R : Type u) [Field k] [Infinite k]
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
        LinearIndependent K (fun i =>
          (1 : K) ⊗ₜ[R] D k R (aeval g (parameterTuple k σ d c i).val)) := by
  obtain ⟨c, hc, h⟩ := exists_parameterTuple_whole_fiber_independent
    k R p g hg d hd q hq
  refine ⟨c, hc, ?_⟩
  intro K _ _ _ _ _ _ hv
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq'
    ((IsScalarTower.algebraMap_eq k (ClosedPoint.CoefficientRing k R p) K).trans
      (by rw [IsScalarTower.algebraMap_eq k R (ClosedPoint.CoefficientRing k R p),
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R
          (ClosedPoint.CoefficientRing k R p) K]))
  have hi := h K hv
  simpa only [← parameterTuple_map,
    residueGeneratorGradient_map_polynomial] using hi

end QuadraticIncidence
