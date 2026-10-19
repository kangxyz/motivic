/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Motivic.Aglib.RingTheory.Bertini.MovingPointBadPointExclusion
import Motivic.Aglib.RingTheory.Bertini.ClosedPointMovingCoefficients
import Lean.Util.CollectAxioms

/-! # One original parameter tuple avoids all charts at a genuine closed point -/
open QuadraticIncidence QuadraticIncidence.MovingPointChart _root_.MvPolynomial

example (k R : Type) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R] (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ : Type} [Fintype σ] (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (f : MvPolynomial (Fin d × Exponent σ) k) (c : Fin d × Exponent σ → k),
      f ≠ 0 ∧ eval c f ≠ 0 ∧ eval c q ≠ 0 ∧
        ∀ (i₀ : Fin d) (j : σ),
          chartParameterMap k R (ClosedPoint.CoefficientRing k R x) g
            (ClosedPoint.selectedValue k R x ∘ g) d i₀ j f = 0 :=
  exists_parameter_choice_avoiding_charts k R (ClosedPoint.CoefficientRing k R x)
    g hg (ClosedPoint.selectedValue k R x ∘ g) d hd q hq

open Lean in
run_cmd do
  for name in #[``trdeg_component_lt, ``exists_nonzero_parameter_relation,
      ``exists_nonzero_common_parameter_relation, ``exists_parameter_choice_avoiding_charts,
      ``linearIndependent_of_parameter_relation_ne_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole-chart ground parameter avoidance: standard foundations only."
