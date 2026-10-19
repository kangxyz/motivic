module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidencePoints

/-! # Genuine bad polynomial points induce maps from the full incidence ring -/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial
universe u
namespace QuadraticIncidence
variable (k R A K : Type u) [CommRing k] [CommRing R] [CommRing A] [Field K]
  [Algebra k R] [Algebra R A] [Algebra R K] [Algebra A K]
  [IsScalarTower R A K] [Algebra.Smooth k R] {σ : Type u} [Fintype σ]

/-- Every original incidence equation vanishes at the monomial coefficients of
an actual polynomial tuple with equal values and a weighted differential relation. -/
theorem parameterCoefficients_ideal_le_ker
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (p : Fin d → restrictTotalDegree σ K 2)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap A K ∘ a) (p i).val)
    (hderiv : ∑ i, algebraMap A K (w i) • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0) :
    LinearIncidence.ideal (ProjectiveIncidence.coefficientMatrix (R := A)
      (coefficientVector k R A g a d w)) ≤
        RingHom.ker (aeval (fun q => (parameterBasis K σ d).repr p q)).toRingHom := by
  apply (ProjectiveIncidence.equations_iff_vector_eq_zero _ _).mpr
  apply (sum_coefficientVector_eq_zero_iff k R A K g a d w _).mpr
  exact sum_parameterCoefficients_eq_zero k R K g (algebraMap A K ∘ a) d
    (algebraMap A K ∘ w) p hvalue hderiv

/-- The actual full (possibly nonreduced) incidence quotient maps to the field
of a bad point, preserving all polynomial parameter coordinates. -/
def pointMap
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (p : Fin d → restrictTotalDegree σ K 2)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap A K ∘ a) (p i).val)
    (hderiv : ∑ i, algebraMap A K (w i) • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0) :
    CoordinateRing k R A g a d w →ₐ[A] K :=
  Ideal.Quotient.liftₐ _ (aeval (fun q => (parameterBasis K σ d).repr p q))
    (fun _ hp => RingHom.mem_ker.mp
      (parameterCoefficients_ideal_le_ker k R A K g a d w p hvalue hderiv hp))

@[simp]
theorem pointMap_coordinates
    (g : σ → R) (a : σ → A) (d : ℕ) (w : Fin d → A)
    (p : Fin d → restrictTotalDegree σ K 2)
    (hvalue : ∀ i, eval (fun j => algebraMap R K (g j)) (p i).val =
      eval (algebraMap A K ∘ a) (p i).val)
    (hderiv : ∑ i, algebraMap A K (w i) • residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l)) (pderiv j (p i).val)) = 0)
    (q : Fin d × Exponent σ) :
    pointMap k R A K g a d w p hvalue hderiv
      (LinearIncidence.coordinates (ProjectiveIncidence.coefficientMatrix (R := A)
        (coefficientVector k R A g a d w)) q) = (parameterBasis K σ d).repr p q := by
  change aeval (fun q => (parameterBasis K σ d).repr p q) (X q) = _
  rw [aeval_X]

end QuadraticIncidence
