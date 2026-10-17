/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberOriginalFunctions
public import Motivic.Aglib.RingTheory.Bertini.CommonResidueFieldExtension
public import Motivic.Aglib.RingTheory.Kaehler.ResidueIndependentSmoothMap

/-! # The same original quadratic projection is smooth along its entire selected fiber -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential MvPolynomial AlgebraicGeometry
universe u
namespace QuadraticIncidence

/-- Polynomial evaluation at an actual algebra-valued point retains the original function. -/
theorem eval_map_original_function {k R K σ : Type u}
    [CommRing k] [CommRing R] [CommRing K] [Algebra k R] [Algebra k K]
    (s : R →ₐ[k] K) (g : σ → R) (p : MvPolynomial σ k) :
    eval (fun j => s (g j)) (MvPolynomial.map (algebraMap k K) p) = s (aeval g p) := by
  rw [eval_map]
  exact (comp_aeval_apply g s p).symm

/-- This is a smooth-near-every-fiber-prime assertion for one unchanged polynomial
projection. It does not assert that the projection is finite or proper. -/
theorem exists_wholeFiber_smooth_projection (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨c, hc, hfield⟩ := exists_originalFunctions_whole_fiber_independent
    k R P g hg d hd q hq
  refine ⟨c, hc, ?_⟩
  let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
  dsimp only
  intro Q hPQ
  apply exists_smooth_one_of_residue_independent k R Q.asIdeal d f hd
  apply independent_differentials_of_same_fiber k R P Q d f hPQ
  intro K _ _ _ _ _ _ hv
  have : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq'
    ((IsScalarTower.algebraMap_eq k (ClosedPoint.CoefficientRing k R P) K).trans
      (by rw [IsScalarTower.algebraMap_eq k R (ClosedPoint.CoefficientRing k R P),
        ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R
          (ClosedPoint.CoefficientRing k R P) K]))
  let s : R →ₐ[k] K := (IsScalarTower.toAlgHom k (ClosedPoint.CoefficientRing k R P) K).comp
    ((Algebra.TensorProduct.includeRight : P.asIdeal.ResidueField →ₐ[k]
      ClosedPoint.CoefficientRing k R P).comp
        (IsScalarTower.toAlgHom k R P.asIdeal.ResidueField))
  apply hfield K
  intro i
  rw [← parameterTuple_map, eval_map_generator_polynomial]
  change algebraMap R K (f i) = eval (fun j => s (g j))
    (MvPolynomial.map (algebraMap k K) (parameterTuple k σ d c i).val)
  rw [eval_map_original_function]
  exact hv i

end QuadraticIncidence
