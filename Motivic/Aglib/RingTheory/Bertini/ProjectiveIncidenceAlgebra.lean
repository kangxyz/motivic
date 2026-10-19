module
public import Motivic.Aglib.RingTheory.Bertini.LinearIncidenceAlgebra
public import Motivic.Aglib.LinearAlgebra.Dual.ProjectiveBaseChange

/-! # A literal incidence algebra with finite-projective equation module

Original duals define the equations before any choice of cotangent basis. They
cut out precisely the vanishing of the universal vector after arbitrary base
change. This retains the original module and allows nonreduced coefficient rings.
-/
@[expose] public noncomputable section
open TensorProduct _root_.MvPolynomial Module
universe u v w
namespace ProjectiveIncidence
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {N : Type w} [Fintype N]

/-- The matrix of all original dual equations, without choosing a free trivialization. -/
def coefficientMatrix (v : N → V) : Matrix (Dual R V) N R := fun φ i => φ (v i)

/-- The actual polynomial quotient by all original dual equations. -/
abbrev CoordinateRing (v : N → V) := LinearIncidence.CoordinateRing (coefficientMatrix (R := R) v)

/-- The universal vector in the base change of the original equation module. -/
def universalVector (v : N → V) : CoordinateRing (R := R) v ⊗[R] V :=
  ∑ i, LinearIncidence.coordinates (coefficientMatrix (R := R) v) i ⊗ₜ[R] v i

/-- The literal quotient imposes vanishing of the whole projective-module vector,
not only of a separately selected list of residue equations. -/
theorem universalVector_eq_zero [Module.Finite R V] [Module.Projective R V] (v : N → V) :
    universalVector (R := R) v = 0 := by
  apply (Dual.forall_baseChange_apply_eq_zero_iff _).mp
  intro φ
  have h := congrFun (LinearIncidence.equations_hold (coefficientMatrix (R := R) v)) φ
  simpa [universalVector, Matrix.mulVec, dotProduct, coefficientMatrix,
    Algebra.smul_def] using h

/-- After any base change, the same original equations mean exactly that the
corresponding vector is zero. This is the defining incidence condition. -/
theorem equations_iff_vector_eq_zero [Module.Finite R V] [Module.Projective R V]
    {A : Type*} [CommRing A] [Algebra R A] (v : N → V) (x : N → A) :
    LinearIncidence.ideal (coefficientMatrix (R := R) v) ≤ RingHom.ker (aeval x).toRingHom ↔
      (∑ i, x i ⊗ₜ[R] v i : A ⊗[R] V) = 0 := by
  rw [← Dual.forall_baseChange_apply_eq_zero_iff]
  rw [LinearIncidence.ideal, Ideal.span_le, Set.range_subset_iff]
  simp [RingHom.mem_ker, LinearIncidence.equation, coefficientMatrix, Algebra.smul_def]

end ProjectiveIncidence
