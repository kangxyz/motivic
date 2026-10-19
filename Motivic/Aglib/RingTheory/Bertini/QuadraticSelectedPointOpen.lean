/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterTuple
public import Motivic.Aglib.RingTheory.Polynomial.Avoidance.MultivariateResidue
public import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # A selected-point open in the original quadratic coefficient space -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module _root_.MvPolynomial TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence

variable {k R L σ : Type u} [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra R L] [Fintype σ]

/-- Actual differential of a quadratic at the specified residue-field point. -/
def selectedDerivative (g : σ → R) :
    restrictTotalDegree σ L 2 →ₗ[L] (L ⊗[R] Ω[R⁄k]) :=
  (LinearMap.snd L L (L ⊗[R] Ω[R⁄k])).comp
    (quadraticResidueJet k R L g (fun i => algebraMap R L (g i))
      (fun i => algebraMap R L (g i)))

/-- Linear monomials in the original generators already realize every cotangent vector. -/
theorem selectedDerivative_surjective (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) :
    Function.Surjective (selectedDerivative (k := k) (L := L) g) := by
  intro v
  obtain ⟨w, hw⟩ := residueGeneratorGradient_surjective k R L g hg v
  let b := fun i => algebraMap R L (g i)
  refine ⟨⟨centeredLinear b w, (mem_restrictTotalDegree σ 2 _).mpr
    ((totalDegree_centeredLinear_le b w).trans (by decide))⟩, ?_⟩
  simpa [selectedDerivative, quadraticResidueJet, quadraticJetParameters, b] using hw

section Determinant
variable {V : Type u} [AddCommGroup V] [Module L V]
  (d : ℕ) (B : Basis (Fin (d + 1)) L V)
  (J : restrictTotalDegree σ L 2 →ₗ[L] V)

/-- Each matrix entry is linear in the same original monomial coefficients. -/
def selectedMatrix : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × Exponent σ) L) :=
  fun i j => ∑ q, C (B.repr (J (parameterBasis L σ d q i)) j.castSucc) * X q

/-- The determinant defining the residue-field principal open. -/
def selectedDeterminant : MvPolynomial (Fin d × Exponent σ) L :=
  (selectedMatrix d B J).det

theorem eval_selectedMatrix (c : Fin d × Exponent σ → L) (i j : Fin d) :
    eval c (selectedMatrix d B J i j) =
      B.repr (J (parameterTuple L σ d c i)) j.castSucc := by
  classical
  simp [selectedMatrix, parameterTuple, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, mul_comm]

theorem eval_selectedDeterminant (c : Fin d × Exponent σ → L) :
    eval c (selectedDeterminant d B J) =
      Matrix.det (fun i j : Fin d => B.repr (J (parameterTuple L σ d c i)) j.castSucc) := by
  rw [selectedDeterminant, RingHom.map_det]
  congr 1
  ext i j
  exact eval_selectedMatrix d B J c i j

/-- The determinant is nonzero because the original derivative map is surjective. -/
theorem selectedDeterminant_ne_zero (hJ : Function.Surjective J) :
    selectedDeterminant d B J ≠ 0 := by
  classical
  choose p hp using fun i : Fin d => hJ (B i.castSucc)
  let c : Fin d × Exponent σ → L := fun q => (parameterBasis L σ d).repr p q
  have hc : parameterTuple L σ d c = p := by
    apply (parameterBasis L σ d).repr.injective
    ext q
    exact parameterTuple_repr L σ d c q
  intro hz
  have he := eval_selectedDeterminant d B J c
  rw [hz, map_zero, hc] at he
  have hm : (fun i j : Fin d => B.repr (J (p i)) j.castSucc) = (1 : Matrix (Fin d) (Fin d) L) := by
    ext i j
    simp [hp, Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  rw [hm, Matrix.det_one] at he
  exact zero_ne_one he

/-- Nonvanishing forces independence of the actual derivatives, not just their coordinates. -/
theorem independent_of_selectedDeterminant (c : Fin d × Exponent σ → L)
    (hc : eval c (selectedDeterminant d B J) ≠ 0) :
    LinearIndependent L (fun i => J (parameterTuple L σ d c i)) := by
  let π : V →ₗ[L] (Fin d → L) :=
    { toFun := fun v j => B.repr v j.castSucc
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply LinearIndependent.of_comp π
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  exact (eval_selectedDeterminant d B J c).symm ▸ hc

end Determinant

/-- A nonzero residue-field polynomial gives a nonzero ground-field condition.
Only implication is asserted; no coefficient-field section is presumed. -/
theorem exists_ground_open [Algebra k L] {τ : Type u}
    (p : MvPolynomial τ L) (hp : p ≠ 0) :
    ∃ q : MvPolynomial τ k, q ≠ 0 ∧
      ∀ c : τ → k, eval c q ≠ 0 → eval (algebraMap k L ∘ c) p ≠ 0 := by
  classical
  have hex : ∃ m, p.coeff m ≠ 0 := by
    by_contra! h
    exact hp (MvPolynomial.ext _ _ fun m => by simpa using h m)
  obtain ⟨m, hm⟩ := hex
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  let q : MvPolynomial τ k := AddMonoidAlgebra.map φ.toAddMonoidHom p
  refine ⟨q, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun a : MvPolynomial τ k => a.coeff m) h
    exact hφ (by simpa [q] using hh)
  · intro c hc hz
    apply hc
    change eval c (AddMonoidAlgebra.map φ.toAddMonoidHom p) = 0
    rw [eval_coefficientLinearMap]
    change φ (eval (algebraMap k L ∘ c) p) = 0
    rw [hz, map_zero]

/-- A principal open in the original parameters guarantees independent actual
cotangent vectors at the selected, possibly nonrational, point. -/
theorem exists_selectedPoint_open [Algebra k L] [Algebra.EssFiniteType k R]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Module.finrank L (L ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c : Fin d × Exponent σ → k, eval c q ≠ 0 →
        LinearIndependent L (fun i => residueGeneratorGradient k R L g
          (fun j => eval (fun l => algebraMap R L (g l))
            (pderiv j (parameterTuple L σ d (algebraMap k L ∘ c) i).val))) := by
  let B := Module.finBasisOfFinrankEq L (L ⊗[R] Ω[R⁄k]) hd
  let J := selectedDerivative (k := k) (L := L) g
  obtain ⟨q, hq, h⟩ := exists_ground_open (k := k) (selectedDeterminant d B J)
    (selectedDeterminant_ne_zero d B J (selectedDerivative_surjective g hg))
  refine ⟨q, hq, fun c hc => ?_⟩
  exact independent_of_selectedDeterminant d B J _ (h c hc)

/-- For the original smooth integral affine model the rank premise is derived,
not retained as a supplier assumption. -/
theorem exists_selectedPoint_open_of_smooth [Algebra k L] [IsDomain R]
    [Algebra.Smooth k R] (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ q : MvPolynomial (Fin d × Exponent σ) k, q ≠ 0 ∧
      ∀ c : Fin d × Exponent σ → k, eval c q ≠ 0 →
        LinearIndependent L (fun i => residueGeneratorGradient k R L g
          (fun j => eval (fun l => algebraMap R L (g l))
            (pderiv j (parameterTuple L σ d (algebraMap k L ∘ c) i).val))) := by
  apply exists_selectedPoint_open g hg d
  rw [Algebra.cotangent_finrank_eq_trdeg_toNat k R L, hd]
  simp

end QuadraticIncidence
