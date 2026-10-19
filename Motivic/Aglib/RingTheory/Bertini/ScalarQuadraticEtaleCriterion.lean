/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.ScalarQuadraticDifferentialMatrix
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion

/-! # Original selected determinant gives an actual scalar-source étale neighborhood -/

@[expose] public noncomputable section

open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
open scoped TensorProduct

namespace QuadraticIncidence

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Nonvanishing of the original residue determinant at the chosen L-coefficients
produces a genuine étale principal neighborhood for that same scalar quadratic map. -/
theorem exists_scalar_quadratic_etale_of_original_determinant
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L] [Algebra.Smooth L (R ⊗[k] L)]
    (x : PrimeSpectrum R) (y : PrimeSpectrum (R ⊗[k] L))
    (hy : PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x)
    {σ : Type u} [Fintype σ] (g : σ → R) (n : ℕ)
    (B : Basis (Fin n) x.asIdeal.ResidueField (x.asIdeal.ResidueField ⊗[R] Ω[R⁄k]))
    (c : Fin n × Exponent σ → L)
    (hc : eval₂ (scalarClosedPointResidueMap k R L x y hy)
      (algebraMap L y.asIdeal.ResidueField ∘ c)
      (fullSelectedDeterminant n B (selectedDerivative (k := k)
        (L := x.asIdeal.ResidueField) g)) ≠ 0) :
    ∃ r ∉ y.asIdeal, ((algebraMap (R ⊗[k] L) (Localization.Away r)).comp
      (aeval (R := L) (fun i => aeval (algebraMap R (R ⊗[k] L) ∘ g)
        (parameterTuple L σ n c i).val)).toRingHom).Etale := by
  let S := R ⊗[k] L
  let K := y.asIdeal.ResidueField
  let B' := scalarClosedPointCotangentBasis k R L x y hy B
  let f : Fin n → S := fun i => aeval (algebraMap R S ∘ g)
    (parameterTuple L σ n c i).val
  let v : Fin n → K ⊗[S] Ω[S⁄L] := fun i => 1 ⊗ₜ[S] D L S (f i)
  have hm : Matrix.det (fun i j : Fin n => B'.repr (v i) j) ≠ 0 := by
    have he : (fun i j : Fin n => B'.repr (v i) j) =
        fun i j => eval₂ (scalarClosedPointResidueMap k R L x y hy)
          (algebraMap L K ∘ c)
          (fullSelectedMatrix n B (selectedDerivative (k := k)
            (L := x.asIdeal.ResidueField) g) i j) := by
      funext i j
      exact scalarQuadraticDifferential_coordinates k R L x y hy g n B c i j
    rw [he]
    change ((eval₂Hom (scalarClosedPointResidueMap k R L x y hy)
      (algebraMap L K ∘ c)).mapMatrix
      (fullSelectedMatrix n B
        (selectedDerivative (k := k) (L := x.asIdeal.ResidueField) g))).det ≠ 0
    rw [← RingHom.map_det]
    exact hc
  let π : (K ⊗[S] Ω[S⁄L]) →ₗ[K] (Fin n → K) :=
    { toFun := fun w j => B'.repr w j
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hi : LinearIndependent K v := by
    apply LinearIndependent.of_comp π
    exact Matrix.linearIndependent_rows_of_det_ne_zero hm
  let b := basisOfLinearIndependentOfCardEqFinrank' v hi
    (by simpa using (Module.finrank_eq_card_basis B').symm)
  exact Algebra.exists_etale_polynomial_map_of_residue_differential_basis
    L S y.asIdeal f b (fun i => Basis.mk_apply _ _ i)

end QuadraticIncidence
