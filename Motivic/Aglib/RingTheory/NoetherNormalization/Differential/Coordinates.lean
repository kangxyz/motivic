module
public import Motivic.Aglib.RingTheory.NoetherNormalization.FiniteElimination.Parameterized
public import Motivic.Aglib.RingTheory.Polynomial.Avoidance.SimultaneousResidue
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Finite-coordinate selection preserving residue-field differential minors

The same parameter determines both the actual finite map on the original quotient
and its tested differential minors. Residue fields need not equal the ground field.
Linear functionals here may be the components of the cotangent differential.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open _root_.MvPolynomial
universe u v w
namespace ParameterizedNoetherNormalization

/-- The actual surviving coordinate of the inverse triangular change. -/
theorem inverse_coordinate (k : Type u) [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) (c : k) (j : Fin n) :
    (coordinateChange f c).symm (X j.succ) =
      X j.succ - c • X (0 : Fin (n + 1)) ^ (2 + f.totalDegree) ^ j.succ.val := by
  simp [coordinateChange, sub_eq_add_neg]

/-- A polynomial whose evaluation is the minor of the actual changed coordinates. -/
def coordinateMinorPolynomial {k : Type u} [Field k] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (K : Type w) [Field K] [Algebra k K]
    (D : Fin d → MvPolynomial (Fin (n + 1)) k →ₗ[k] K) (j : Fin d → Fin n) :
    Polynomial K :=
  Matrix.det fun a b => Polynomial.C (D a (X (j b).succ)) -
    Polynomial.X * Polynomial.C
      (D a (X (0 : Fin (n + 1)) ^ (2 + f.totalDegree) ^ (j b).succ.val))

/-- Evaluation computes the differential minor of precisely the coordinates used
in the finite original-quotient map. -/
theorem coordinateMinorPolynomial_eval {k : Type u} [Field k] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (K : Type w) [Field K] [Algebra k K]
    (D : Fin d → MvPolynomial (Fin (n + 1)) k →ₗ[k] K) (j : Fin d → Fin n)
    (c : k) :
    (coordinateMinorPolynomial f K D j).eval (algebraMap k K c) =
      Matrix.det (fun a b => D a ((coordinateChange f c).symm (X (j b).succ))) := by
  change (Polynomial.evalRingHom (algebraMap k K c))
    (coordinateMinorPolynomial f K D j) = _
  rw [coordinateMinorPolynomial, RingHom.map_det]
  congr 1
  ext a b
  rw [inverse_coordinate, map_sub, map_smul]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  change Polynomial.eval _ (_ - _ * _) = _
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Algebra.smul_def]

/-- Over an infinite field, one actual finite projection preserves finitely many
specified nonzero cotangent minors, in arbitrary residue-field extensions. -/
theorem exists_finite_projection_preserving_differential_minors
    {k : Type u} [Field k] [Infinite k] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (D : (i : ι) → Fin d → MvPolynomial (Fin (n + 1)) k →ₗ[k] K i)
    (j : ι → Fin d → Fin n)
    (hD : ∀ i, Matrix.det (fun a b => D i a (X (j i b).succ)) ≠ 0) :
    ∃ c : k, c ≠ 0 ∧
      ((Ideal.Quotient.mkₐ k I).comp
        ((coordinateChange f c).symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∀ i, Matrix.det
        (fun a b => D i a ((coordinateChange f c).symm (X (j i b).succ))) ≠ 0 := by
  obtain ⟨c, hc, hminor⟩ := Polynomial.exists_nonzero_scalar_preserving_residue_conditions
    k K (fun i => coordinateMinorPolynomial f (K i) (D i) (j i)) (fun i => by
      have h := coordinateMinorPolynomial_eval f (K i) (D i) (j i) 0
      simp only [map_zero, coordinateChange_zero, AlgEquiv.refl_symm,
        AlgEquiv.coe_refl] at h
      rw [h]
      exact hD i)
  refine ⟨c, hc, coordinateChange_finite_projection f I c hc hf hIf, ?_⟩
  intro i
  simpa only [coordinateMinorPolynomial_eval] using hminor i

end ParameterizedNoetherNormalization
