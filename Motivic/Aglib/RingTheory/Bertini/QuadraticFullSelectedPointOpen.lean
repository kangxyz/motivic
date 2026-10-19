/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticSelectedPointOpen

/-! # Full-rank selected-point condition in the same compactifying quadratic tuple -/
@[expose] public noncomputable section
open Module _root_.MvPolynomial TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence
variable {k R L σ : Type u} [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra R L] [Fintype σ]
section Determinant
variable {V : Type u} [AddCommGroup V] [Module L V]
  (d : ℕ) (B : Basis (Fin d) L V)
  (J : restrictTotalDegree σ L 2 →ₗ[L] V)

/-- Each matrix entry is linear in the same original monomial coefficients. -/
def fullSelectedMatrix : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Exponent σ) L) :=
  fun i j => ∑ q, C (B.repr (J (parameterBasis L σ d q i)) j) * X q

/-- The determinant defining the residue-field principal open. -/
def fullSelectedDeterminant : MvPolynomial (Fin d × Exponent σ) L :=
  (fullSelectedMatrix d B J).det

theorem eval_fullSelectedMatrix (c : Fin d × Exponent σ → L) (i j : Fin d) :
    eval c (fullSelectedMatrix d B J i j) =
      B.repr (J (parameterTuple L σ d c i)) j := by
  classical
  simp [fullSelectedMatrix, parameterTuple, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, mul_comm]

theorem eval_fullSelectedDeterminant (c : Fin d × Exponent σ → L) :
    eval c (fullSelectedDeterminant d B J) =
      Matrix.det (fun i j : Fin d => B.repr (J (parameterTuple L σ d c i)) j) := by
  rw [fullSelectedDeterminant, RingHom.map_det]
  congr 1
  ext i j
  exact eval_fullSelectedMatrix d B J c i j

/-- The determinant is nonzero because the original derivative map is surjective. -/
theorem fullSelectedDeterminant_ne_zero (hJ : Function.Surjective J) :
    fullSelectedDeterminant d B J ≠ 0 := by
  classical
  choose p hp using fun i : Fin d => hJ (B i)
  let c : Fin d × Exponent σ → L := fun q => (parameterBasis L σ d).repr p q
  have hc : parameterTuple L σ d c = p := by
    apply (parameterBasis L σ d).repr.injective
    ext q
    exact parameterTuple_repr L σ d c q
  intro hz
  have he := eval_fullSelectedDeterminant d B J c
  rw [hz, map_zero, hc] at he
  have hm : (fun i j : Fin d => B.repr (J (p i)) j) = (1 : Matrix (Fin d) (Fin d) L) := by
    ext i j
    simp [hp, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  rw [hm, Matrix.det_one] at he
  exact zero_ne_one he

/-- Nonvanishing forces independence of the actual derivatives, not just their coordinates. -/
theorem independent_of_fullSelectedDeterminant (c : Fin d × Exponent σ → L)
    (hc : eval c (fullSelectedDeterminant d B J) ≠ 0) :
    LinearIndependent L (fun i => J (parameterTuple L σ d c i)) := by
  let π : V →ₗ[L] (Fin d → L) :=
    { toFun := fun v j => B.repr v j
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply LinearIndependent.of_comp π
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  exact (eval_fullSelectedDeterminant d B J c).symm ▸ hc

end Determinant

/-- All rows of the same quadratic tuple have full original cotangent rank on
one nonempty ground principal open, without assuming a rational selected point. -/
theorem exists_fullSelectedPoint_open [Algebra k L] [IsDomain R]
    [Algebra.Smooth k R] (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (d : ℕ) (hd : Algebra.trdeg k R = d) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c : Fin d × Exponent σ → k, eval c q ≠ 0 →
        LinearIndependent L (fun i => selectedDerivative (k := k) (L := L) g
          (parameterTuple L σ d (algebraMap k L ∘ c) i)) := by
  have hr : Module.finrank L (L ⊗[R] Ω[R⁄k]) = d := by
    rw [Algebra.cotangent_finrank_eq_trdeg_toNat k R L, hd]
    simp
  let B := Module.finBasisOfFinrankEq L (L ⊗[R] Ω[R⁄k]) hr
  let J := selectedDerivative (k := k) (L := L) g
  obtain ⟨q, hq, h⟩ := exists_ground_open (k := k) (fullSelectedDeterminant d B J)
    (fullSelectedDeterminant_ne_zero d B J (selectedDerivative_surjective g hg))
  exact ⟨q, hq, fun c hc => independent_of_fullSelectedDeterminant d B J _ (h c hc)⟩

end QuadraticIncidence
