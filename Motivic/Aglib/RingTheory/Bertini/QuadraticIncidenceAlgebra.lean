module
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveIncidenceAlgebra
public import Motivic.Aglib.RingTheory.Bertini.QuadraticResidueIncidence
public import Mathlib.RingTheory.Smooth.Basic

/-! # The original affine embedding's universal quadratic bad-fiber equations

The coefficient algebra can be the actual moving-point and normalized-left-kernel
chart. The parameter variables are the fixed quadratic monomials, and the
cotangent module is that of the original affine algebra, without a new chart.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial Module TensorProduct KaehlerDifferential
universe u v w z
namespace QuadraticIncidence

/-- Quadratic monomials have an index set independent of the coefficient ring. -/
abbrev Exponent (σ : Type z) := {e : σ →₀ ℕ // e.sum (fun _ n => n) ≤ 2}

instance {σ : Type z} [Finite σ] : Finite (Exponent σ) := by
  let b : Basis (Exponent σ) ℚ (restrictTotalDegree σ ℚ 2) := basisRestrictSupport ℚ _
  exact Module.Finite.finite_basis b

instance {σ : Type z} [Finite σ] : Fintype (Exponent σ) := Fintype.ofFinite _

/-- The original monomial basis of the quadratic parameter module. -/
def monomialBasis (A : Type w) [CommRing A] (σ : Type z) :
    Basis (Exponent σ) A (restrictTotalDegree σ A 2) := basisRestrictSupport A _

variable (k : Type u) (R : Type v) (A : Type w)
  [CommRing k] [CommRing R] [CommRing A] [Algebra k R] [Algebra R A]
  {σ : Type z} [Fintype σ]

/-- The actual value-difference and weighted cotangent coefficient of one
quadratic monomial in one projection coordinate. -/
def coefficientVector (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (q : Fin d × Exponent σ) : (Fin d → A) × (A ⊗[R] Ω[R⁄k]) :=
  let p := monomial q.2.val (1 : A)
  let b := fun i => algebraMap R A (g i)
  (Pi.single q.1 (eval b p - eval a p),
    w q.1 • residueGeneratorGradient k R A g (fun i => eval b (pderiv i p)))

/-- The literal polynomial quotient imposing the original bad-fiber equations. -/
abbrev CoordinateRing (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A) :=
  ProjectiveIncidence.CoordinateRing (R := A) (coefficientVector k R A g a d w)

/-- In the universal quotient, the full original value and cotangent vector
vanishes. This is derived from smoothness, not supplied as a family premise. -/
theorem universal_equations [Algebra.Smooth k R]
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A) :
    ProjectiveIncidence.universalVector (R := A) (coefficientVector k R A g a d w) = 0 :=
  ProjectiveIncidence.universalVector_eq_zero (R := A) _

end QuadraticIncidence
