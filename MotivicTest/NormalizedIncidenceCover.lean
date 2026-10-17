module
import Motivic.Aglib.RingTheory.Bertini.NormalizedIncidenceCover
import Motivic.Aglib.RingTheory.Bertini.QuadraticResidueIncidence
import Lean.Util.CollectAxioms

/-! # Every actual dependent cotangent family has a normalized chart witness -/
open Module TensorProduct KaehlerDifferential

example (k R K : Type) [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] (d : ℕ)
    (v : Fin d → K ⊗[R] Ω[R⁄k]) (h : ¬ LinearIndependent K v) :
    ∃ (i₀ : Fin d) (w : Fin d → K), w i₀ = 1 ∧ ∑ i, w i • v i = 0 :=
  LinearMap.exists_normalized_relation_of_not_linearIndependent v h

open LinearMap Lean in
run_cmd do
  for name in #[``exists_normalized_relation_of_not_linearIndependent,
      ``not_linearIndependent_iff_normalized_relation] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Normalized incidence chart cover: standard foundations only."
