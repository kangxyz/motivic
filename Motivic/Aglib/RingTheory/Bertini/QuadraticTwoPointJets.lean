module
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Quadratic first jets on fibers through a prescribed point

For every second point distinct from the prescribed point, quadratics vanishing
at both points realize every ambient cotangent vector at the second point.
This is the two-point interpolation input for the whole-fiber incidence argument,
not a claim that nonzero Jacobians at finitely many points imply good fibers.
-/
@[expose] public noncomputable section
open MvPolynomial
universe u v
namespace MvPolynomial
section Linear
variable {K : Type u} [CommRing K] {σ : Type v} [Fintype σ]

/-- An actual linear polynomial centered at the second geometric point. -/
def centeredLinear (b v : σ → K) : MvPolynomial σ K :=
  ∑ i, C (v i) * (X i - C (b i))

@[simp]
theorem eval_centeredLinear_self (b v : σ → K) : eval b (centeredLinear b v) = 0 := by
  simp [centeredLinear]

@[simp]
theorem eval_pderiv_centeredLinear (b v : σ → K) (i : σ) :
    eval b (pderiv i (centeredLinear b v)) = v i := by
  classical
  simp [centeredLinear, Derivation.leibniz, Pi.single_apply, smul_eq_mul]

theorem totalDegree_centeredLinear_le (b v : σ → K) :
    (centeredLinear b v).totalDegree ≤ 1 := by
  nontriviality K using Subsingleton.eq_zero (α := MvPolynomial σ K)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by
    simpa using totalDegree_sub_C_le (X i : MvPolynomial σ K) (b i))

end Linear

variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]

/-- An explicit quadratic preserving both point values and prescribing the second jet. -/
def twoPointQuadratic (a b v : σ → K) (j : σ) : MvPolynomial σ K :=
  C ((b j - a j)⁻¹) * (X j - C (a j)) * centeredLinear b v

@[simp]
theorem eval_twoPointQuadratic_first (a b v : σ → K) (j : σ) :
    eval a (twoPointQuadratic a b v j) = 0 := by simp [twoPointQuadratic]

@[simp]
theorem eval_twoPointQuadratic_second (a b v : σ → K) (j : σ) :
    eval b (twoPointQuadratic a b v j) = 0 := by simp [twoPointQuadratic]

theorem eval_pderiv_twoPointQuadratic (a b v : σ → K) (j : σ)
    (hj : b j ≠ a j) (i : σ) :
    eval b (pderiv i (twoPointQuadratic a b v j)) = v i := by
  simp [twoPointQuadratic, Derivation.leibniz, smul_eq_mul, sub_ne_zero.mpr hj]

theorem totalDegree_twoPointQuadratic_le (a b v : σ → K) (j : σ) :
    (twoPointQuadratic a b v j).totalDegree ≤ 2 := by
  apply (totalDegree_mul _ _).trans
  have hleft : (C ((b j - a j)⁻¹) * (X j - C (a j)) :
      MvPolynomial σ K).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by
      simpa using totalDegree_sub_C_le (X j : MvPolynomial σ K) (a j))
  exact (Nat.add_le_add hleft (totalDegree_centeredLinear_le b v)).trans (by decide)

omit [Fintype σ] in
/-- The jet-surjectivity statement holds for every distinct geometric point,
with no rationality or characteristic restriction on the coefficient field. -/
theorem exists_quadratic_two_point_jet [Finite σ] (a b : σ → K) (hab : a ≠ b) (v : σ → K) :
    ∃ f : MvPolynomial σ K, f.totalDegree ≤ 2 ∧ eval a f = 0 ∧ eval b f = 0 ∧
      ∀ i, eval b (pderiv i f) = v i := by
  let := Fintype.ofFinite σ
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
  exact ⟨twoPointQuadratic a b v j, totalDegree_twoPointQuadratic_le a b v j,
    eval_twoPointQuadratic_first a b v j, eval_twoPointQuadratic_second a b v j,
    eval_pderiv_twoPointQuadratic a b v j (Ne.symm hj)⟩

omit [Fintype σ] in
/-- Quadratic parameters prescribe the value difference and the entire second first jet.
The first point is arbitrary, and the second ranges over its whole ambient complement. -/
theorem exists_quadratic_value_difference_jet [Finite σ]
    (a b : σ → K) (hab : a ≠ b) (c : K) (v : σ → K) :
    ∃ f : MvPolynomial σ K, f.totalDegree ≤ 2 ∧ eval b f - eval a f = c ∧
      ∀ i, eval b (pderiv i f) = v i := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
  let l : MvPolynomial σ K := C (c / (b j - a j)) * (X j - C (a j))
  have hl : l.totalDegree ≤ 1 := (totalDegree_mul _ _).trans (by
    simpa using totalDegree_sub_C_le (X j : MvPolynomial σ K) (a j))
  have hla : eval a l = 0 := by simp [l]
  have hlb : eval b l = c := by
    simp [l, div_mul_cancel₀ c (sub_ne_zero.mpr (Ne.symm hj))]
  obtain ⟨q, hq, hqa, hqb, hqd⟩ := exists_quadratic_two_point_jet a b hab
    (fun i => v i - eval b (pderiv i l))
  refine ⟨l + q, (totalDegree_add _ _).trans (max_le (hl.trans (by decide)) hq),
    ?_, ?_⟩
  · simp [hla, hlb, hqa, hqb]
  · intro i
    simp [hqd]

end MvPolynomial
