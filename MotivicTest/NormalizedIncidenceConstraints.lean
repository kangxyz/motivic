module
import Motivic.Aglib.RingTheory.Bertini.NormalizedIncidenceConstraints
import Motivic.Aglib.RingTheory.Bertini.QuadraticJetParameters
import Lean.Util.CollectAxioms

/-! # Actual quadratic parameters in a normalized bad-fiber incidence chart -/
open MvPolynomial LinearMap

example (K : Type) [Field K] {σ ι : Type} [Finite σ] [Fintype ι]
    (a b : σ → K) (hab : a ≠ b) (w : ι → K) (i₀ : ι) (hw : w i₀ = 1) :
    Function.Surjective (normalizedJetConstraints (quadraticJetParameters a b) w) :=
  normalizedJetConstraints_surjective _ (quadraticJetParameters_surjective a b hab) w i₀ hw

example (K : Type) [Field K] {σ ι : Type} [Fintype σ] [Fintype ι]
    (a b : σ → K) (hab : a ≠ b) (w : ι → K) (i₀ : ι) (hw : w i₀ = 1) :
    Fintype.card ι + Fintype.card σ +
      Module.finrank K (normalizedJetConstraints (quadraticJetParameters a b) w).ker =
        Module.finrank K (ι → restrictTotalDegree σ K 2) := by
  simpa using finrank_ker_normalizedJetConstraints _
    (quadraticJetParameters_surjective a b hab) w i₀ hw

open Lean in
run_cmd do
  for name in #[``normalizedJetConstraints_surjective,
      ``finrank_ker_normalizedJetConstraints] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Normalized incidence constraints: standard foundations only."
