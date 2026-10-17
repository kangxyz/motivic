module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceRank
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveIncidenceDimension

/-! # Transcendence degree of the actual quadratic incidence fiber -/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence
variable (k R K : Type u) [CommRing k] [CommRing R] [Field K]
  [Algebra k R] [Algebra R K] [Algebra.EssFiniteType k R]
  {σ : Type u} [Fintype σ]

/-- The full incidence quotient has `2d+1` fewer transcendental parameters.
Its equations and their rank come from the original embedding, not from a
supplied matrix, relation, smooth chart, or dimension estimate for the quotient. -/
theorem trdeg_coordinateRing_add_constraints_le (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a : σ → K)
    (hab : a ≠ fun i => algebraMap R K (g i)) (d : ℕ)
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1)
    (w : Fin d → K) (i₀ : Fin d) (hw : w i₀ = 1) :
    Algebra.trdeg K (CoordinateRing k R K g a d w) + ((2 * d + 1 : ℕ) : Cardinal.{u}) ≤
      (d * Fintype.card (Exponent σ) : ℕ) := by
  have h := ProjectiveIncidence.trdeg_coordinateRing_add_finrank_le
    (coefficientVector k R K g a d w) (span_coefficientVector k R K g hg a hab d w i₀ hw)
  simpa [Module.finrank_prod, hd, two_mul, Nat.add_assoc] using h

end QuadraticIncidence
