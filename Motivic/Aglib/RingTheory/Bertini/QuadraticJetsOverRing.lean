module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticTwoPointJets

/-! # Two-point quadratic interpolation over an actual principal chart

An inverse of one coordinate difference suffices over any coefficient ring.
Thus the interpolation works in families on the principal charts of the
complement of the diagonal, not only separately over residue fields.
-/
@[expose] public noncomputable section
namespace MvPolynomial
universe u v
variable {R : Type u} [CommRing R] {σ : Type v} [Fintype σ]

/-- The quadratic interpolation term on a chart where one difference is invertible. -/
def twoPointQuadraticChart (a b v : σ → R) (j : σ) (e : R) : MvPolynomial σ R :=
  C e * (X j - C (a j)) * centeredLinear b v

@[simp]
theorem eval_twoPointQuadraticChart_first (a b v : σ → R) (j : σ) (e : R) :
    eval a (twoPointQuadraticChart a b v j e) = 0 := by
  simp [twoPointQuadraticChart]

@[simp]
theorem eval_twoPointQuadraticChart_second (a b v : σ → R) (j : σ) (e : R) :
    eval b (twoPointQuadraticChart a b v j e) = 0 := by
  simp [twoPointQuadraticChart]

theorem eval_pderiv_twoPointQuadraticChart (a b v : σ → R) (j : σ) (e : R)
    (he : e * (b j - a j) = 1) (i : σ) :
    eval b (pderiv i (twoPointQuadraticChart a b v j e)) = v i := by
  simp [twoPointQuadraticChart, Derivation.leibniz, smul_eq_mul, ← mul_assoc, he]

theorem totalDegree_twoPointQuadraticChart_le (a b v : σ → R) (j : σ) (e : R) :
    (twoPointQuadraticChart a b v j e).totalDegree ≤ 2 := by
  nontriviality R using Subsingleton.eq_zero (α := MvPolynomial σ R)
  apply (totalDegree_mul _ _).trans
  have hleft : (C e * (X j - C (a j)) : MvPolynomial σ R).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add, totalDegree_X] using
        totalDegree_sub_C_le (X j : MvPolynomial σ R) (a j))
  exact (Nat.add_le_add hleft (totalDegree_centeredLinear_le b v)).trans (by decide)

omit [Fintype σ] in
/-- The same chart realizes all value and derivative constraints over arbitrary rings. -/
theorem exists_quadratic_value_difference_jet_of_inverse [Finite σ]
    (a b : σ → R) (j : σ) (e : R) (he : e * (b j - a j) = 1)
    (c : R) (v : σ → R) :
    ∃ f : MvPolynomial σ R, f.totalDegree ≤ 2 ∧ eval b f - eval a f = c ∧
      ∀ i, eval b (pderiv i f) = v i := by
  nontriviality R using Subsingleton.eq_zero (α := MvPolynomial σ R)
  let := Fintype.ofFinite σ
  let l : MvPolynomial σ R := C (c * e) * (X j - C (a j))
  have hl : l.totalDegree ≤ 1 := (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C, zero_add, totalDegree_X] using
        totalDegree_sub_C_le (X j : MvPolynomial σ R) (a j))
  have hla : eval a l = 0 := by simp [l]
  have hlb : eval b l = c := by simp [l, mul_assoc, he]
  let q := twoPointQuadraticChart a b (fun i => v i - eval b (pderiv i l)) j e
  have hqa : eval a q = 0 := eval_twoPointQuadraticChart_first ..
  have hqb : eval b q = 0 := eval_twoPointQuadraticChart_second ..
  have hqd (i : σ) : eval b (pderiv i q) = v i - eval b (pderiv i l) :=
    eval_pderiv_twoPointQuadraticChart _ _ _ _ _ he i
  refine ⟨l + q, (totalDegree_add _ _).trans (max_le (hl.trans (by decide))
    (totalDegree_twoPointQuadraticChart_le ..)), ?_, ?_⟩
  · simp [hla, hlb, hqa, hqb]
  · intro i
    simp [hqd]

end MvPolynomial
