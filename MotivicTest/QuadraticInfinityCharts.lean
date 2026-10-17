/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityCharts
public import Lean

/-! # The original monomial-ratio infinity charts retain nonreduced quotients -/
public noncomputable section
universe u
open QuadraticIncidence InfinityChart

example (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    {σ : Type u} (g : σ → R) (j : Exponent σ)
    (hj : monomialFunction k R g j ≠ 0) {d : ℕ}
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    Algebra.trdeg k ((chart k R g j) ⧸
      Ideal.span {infinityCoordinate k R g j}) ≤ d := by
  exact trdeg_infinity_quotient_le k R g j hj _
    (Ideal.subset_span (Set.mem_singleton _)) hd

open Lean in
run_cmd do
  for name in #[``trdeg_infinity_quotient_le, ``trdeg_chart_le,
      ``chart_eq_adjoin_ratios, ``ratio_self] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual quadratic ratio chart and full infinity quotient: standard foundations only."
