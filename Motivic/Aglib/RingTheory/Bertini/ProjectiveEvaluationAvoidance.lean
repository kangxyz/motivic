/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveEvaluationDimension

/-! # Parameter relations exclude actual common zeros of the unchanged linear forms -/
@[expose] public noncomputable section
open MvPolynomial
universe u
namespace ProjectiveEvaluationIncidence
variable (k A K : Type u) [Field k] [CommRing A] [Field K]
  [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
  {N : Type u} [Fintype N]

/-- Evaluation of a genuine point satisfying all original homogeneous equations. -/
def pointMap (a : N → A) (n : ℕ) (c : Fin n × N → k)
    (hc : ∀ i, ∑ e, algebraMap k K (c (i, e)) * algebraMap A K (a e) = 0) :
    Ring A a n →ₐ[A] K := by
  classical
  apply Ideal.Quotient.liftₐ _ (aeval (algebraMap k K ∘ c))
  intro f hf
  have hk : LinearIncidence.ideal (matrix A a n) ≤
      RingHom.ker (aeval (algebraMap k K ∘ c)).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change aeval (algebraMap k K ∘ c) (LinearIncidence.equation (matrix A a n) i) = 0
    simpa [LinearIncidence.equation, matrix, Fintype.sum_prod_type, apply_ite, mul_comm] using hc i
  exact hk hf

/-- The quotient evaluation preserves the original ground-parameter polynomial. -/
theorem pointMap_parameterMap (a : N → A) (n : ℕ) (c : Fin n × N → k)
    (hc : ∀ i, ∑ e, algebraMap k K (c (i, e)) * algebraMap A K (a e) = 0)
    (f : MvPolynomial (Fin n × N) k) :
    pointMap k A K a n c hc (parameterMap A k a n f) =
      algebraMap k K (eval c f) := by
  have he : (pointMap k A K a n c hc).toRingHom.comp
      (parameterMap A k a n).toRingHom =
      (algebraMap k K).comp (eval c) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, parameterMap,
        aeval_C, eval_C]
      change pointMap k A K a n c hc (algebraMap k (Ring A a n) r) = _
      rw [IsScalarTower.algebraMap_apply k A (Ring A a n), AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, parameterMap,
        aeval_X, eval_X]
      change aeval (algebraMap k K ∘ c) (X q) = _
      simp
  exact DFunLike.congr_fun he f

/-- A nonvanishing original parameter relation rules out all actual common zeros. -/
theorem not_vanish_of_relation (a : N → A) (n : ℕ)
    (f : MvPolynomial (Fin n × N) k) (hf : parameterMap A k a n f = 0)
    (c : Fin n × N → k) (hc : eval c f ≠ 0) :
    ¬ ∀ i, ∑ e, algebraMap k K (c (i, e)) * algebraMap A K (a e) = 0 := by
  intro hzero
  have hz := congrArg (pointMap k A K a n c hzero) hf
  have he := pointMap_parameterMap k A K a n c hzero f
  have hz' := he.symm.trans hz
  exact hc ((algebraMap k K).injective (by simpa using hz'))

end ProjectiveEvaluationIncidence
