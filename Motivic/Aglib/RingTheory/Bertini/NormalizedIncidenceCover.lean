module
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Normalized left-kernel charts cover every rank-deficient fiber

The witness is obtained from actual linear dependence. Its distinguished
coefficient is one, so no rationality condition or chosen nonzero kernel vector
is imposed on the original fiber.
-/
@[expose] public noncomputable section

namespace LinearMap
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- Every dependent finite family lies on a normalized left-kernel chart. -/
theorem exists_normalized_relation_of_not_linearIndependent (v : ι → V)
    (h : ¬ LinearIndependent K v) :
    ∃ (i₀ : ι) (w : ι → K), w i₀ = 1 ∧ ∑ i, w i • v i = 0 := by
  obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp h
  refine ⟨i₀, fun i => (c i₀)⁻¹ * c i, inv_mul_cancel₀ hi₀, ?_⟩
  simp_rw [mul_smul]
  rw [← Finset.smul_sum, hc, smul_zero]

/-- The normalized charts detect precisely failure of independence, including
an empty indexing type without an artificial positivity hypothesis. -/
theorem not_linearIndependent_iff_normalized_relation (v : ι → V) :
    ¬ LinearIndependent K v ↔
      ∃ (i₀ : ι) (w : ι → K), w i₀ = 1 ∧ ∑ i, w i • v i = 0 := by
  refine ⟨exists_normalized_relation_of_not_linearIndependent v, ?_⟩
  rintro ⟨i₀, w, hw, he⟩ h
  have hz := Fintype.linearIndependent_iff.mp h w he i₀
  exact one_ne_zero (hw.symm.trans hz)

end LinearMap
