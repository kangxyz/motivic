module
import Motivic.Aglib.RingTheory.Bertini.NormalizedMovingPointEvaluation
import Lean.Util.CollectAxioms

/-! # Actual chart evaluation and its unchanged normalized coordinates -/
open QuadraticIncidence.MovingPointChart

example (B K : Type) [CommRing B] [Field K] [Algebra B K]
    (d : ℕ) (i₀ : Fin d) (t : B) (w : Fin d → K)
    (ht : algebraMap B K t ≠ 0) (hw : w i₀ = 1) (i : Fin d) :
    evaluate B d i₀ t K w ht (weight B d i₀ t i) = w i :=
  evaluate_weight B d i₀ t K w ht hw i

open Lean in
run_cmd do
  for name in #[``weight_distinguished, ``difference_isUnit, ``difference_ne_zero,
      ``card_weightIndex, ``evaluate, ``evaluate_weight] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual normalized moving-point charts: standard foundations only."
