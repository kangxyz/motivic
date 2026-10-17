module
import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceDimension
import Lean.Util.CollectAxioms

/-! # Direct use and foundation audit of the actual incidence fiber bound -/
open Module TensorProduct KaehlerDifferential

example (k R K : Type) [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra.EssFiniteType k R]
    {σ : Type} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a : σ → K)
    (hab : a ≠ fun i => algebraMap R K (g i)) (d : ℕ)
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1)
    (w : Fin d → K) (i₀ : Fin d) (hw : w i₀ = 1) :
    Algebra.trdeg K (QuadraticIncidence.CoordinateRing k R K g a d w) +
      ((2 * d + 1 : ℕ) : Cardinal) ≤
      (d * Fintype.card (QuadraticIncidence.Exponent σ) : ℕ) :=
  QuadraticIncidence.trdeg_coordinateRing_add_constraints_le k R K g hg a hab d hd w i₀ hw

open QuadraticIncidence ProjectiveIncidence in
open Lean in
run_cmd do
  for name in #[``monomialBasis_coe, ``parameterBasis_apply,
      ``coefficientVector_eq_constraint, ``span_coefficientVector,
      ``trdeg_coordinateRing_add_finrank_le, ``trdeg_coordinateRing_add_constraints_le] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual quadratic incidence fiber bound: standard foundations only."
