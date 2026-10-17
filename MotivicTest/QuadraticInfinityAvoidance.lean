/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityAvoidance
public import Lean

/-! # Actual all-chart, all-field infinity avoidance in the unchanged parameter family -/
public noncomputable section
open MvPolynomial QuadraticIncidence InfinityChart
universe u

example (k R : Type u) [Field k] [Infinite k] [CommRing R] [IsDomain R] [Algebra k R]
    {σ : Type u} [Finite σ] (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1)
    (q : MvPolynomial (Fin (d + 1) × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin (d + 1) × Exponent σ → k,
      eval c q ≠ 0 ∧ NoCommonInfinityZero k R g d c := by
  obtain ⟨f, c, _, hc, hq', hz⟩ :=
    exists_parameters_avoiding_infinity_relations k R g d hd q hq
  exact ⟨c, hq', noCommonInfinityZero_of_relation k R g d f hz c hc⟩

open Lean in
run_cmd do
  for name in #[``exists_infinity_avoidance_polynomial,
      ``exists_parameters_avoiding_infinity_relations,
      ``noCommonInfinityZero_of_relation,
      ``ProjectiveEvaluationIncidence.exists_nonzero_parameter_relation,
      ``ProjectiveEvaluationIncidence.pointMap_parameterMap] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Same quadratic family, all actual infinity fields: standard foundations only."
