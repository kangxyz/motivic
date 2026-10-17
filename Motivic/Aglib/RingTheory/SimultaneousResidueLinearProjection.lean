module
public import Motivic.Aglib.RingTheory.SimultaneousResidueMultivariateAvoidance
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # One linear projection nonsingular at finitely many residue fields

Full row-rank matrices over arbitrary residue extensions admit a single matrix
of ground-field coefficients making all resulting square determinants nonzero.
This is the simultaneous linear-coordinate selection used before finite elimination.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Matrix
universe u v w z
namespace Matrix

/-- The generic determinant of a projected matrix. -/
def projectionDeterminant {K : Type w} [Field K] {d : ℕ} {μ : Type z} [Fintype μ]
    (A : Matrix (Fin d) (μ) K) : MvPolynomial (μ × Fin d) K :=
  Matrix.det (fun a b => ∑ j, MvPolynomial.C (A a j) * MvPolynomial.X (j, b))

/-- Specializing the generic determinant gives the literal matrix product. -/
theorem projectionDeterminant_eval {K : Type w} [Field K] {d : ℕ} {μ : Type z} [Fintype μ]
    (A : Matrix (Fin d) (μ) K) (B : Matrix (μ) (Fin d) K) :
    MvPolynomial.eval (fun p => B p.1 p.2) (projectionDeterminant A) =
      Matrix.det (A * B) := by
  rw [projectionDeterminant, RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply]

/-- Surjectivity of the original differential matrix makes the generic minor
nonzero, without imposing rationality of the underlying point. -/
theorem projectionDeterminant_ne_zero {K : Type w} [Field K] {d : ℕ} {μ : Type z} [Fintype μ]
    (A : Matrix (Fin d) (μ) K) (hA : Function.Surjective A.mulVec) :
    projectionDeterminant A ≠ 0 := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  intro h
  have hh := projectionDeterminant_eval A B
  simp [h, hB] at hh

/-- A single ground-field linear projection is nonsingular simultaneously at all
of the given residue fields. The only field-size assumption is `Infinite k`. -/
theorem exists_simultaneous_residue_linear_projection
    (k : Type u) [Field k] [Infinite k] {ι : Type v} [Finite ι] {d : ℕ} {μ : Type z} [Fintype μ]
    (K : ι → Type w) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (A : (i : ι) → Matrix (Fin d) (μ) (K i))
    (hA : ∀ i, Function.Surjective (A i).mulVec) :
    ∃ B : Matrix (μ) (Fin d) k,
      ∀ i, Matrix.det (A i * B.map (algebraMap k (K i))) ≠ 0 := by
  obtain ⟨x, hx⟩ := MvPolynomial.exists_ground_specialization_avoiding_residue_polynomials
    k K (fun i => projectionDeterminant (A i))
      (fun i => projectionDeterminant_ne_zero (A i) (hA i))
  refine ⟨fun a b => x (a, b), fun i => ?_⟩
  have h := projectionDeterminant_eval (A i)
    (Matrix.map (fun a b => x (a, b) : Matrix (μ) (Fin d) k)
      (algebraMap k (K i)))
  rw [← h]
  exact hx i

end Matrix
