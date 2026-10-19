/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Motivic.Aglib.RingTheory.Bertini.WholeOffDiagonalFiberParameters
import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterBaseChange
import Motivic.Aglib.RingTheory.Bertini.ClosedPointMovingCoefficients
import Lean.Util.CollectAxioms

/-! # Actual ground parameters uniformly control the original closed-point fiber -/
open QuadraticIncidence _root_.MvPolynomial

example (k R : Type) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R] (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    {σ : Type} [Fintype σ] (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      GoodOffDiagonalParameters k R (ClosedPoint.CoefficientRing k R x) g
        (ClosedPoint.selectedValue k R x ∘ g) d c :=
  exists_goodOffDiagonalParameters k R (ClosedPoint.CoefficientRing k R x) g hg
    (ClosedPoint.selectedValue k R x ∘ g) d hd q hq

example (k K : Type) [Field k] [Field K] [Algebra k K]
    (σ : Type) [Fintype σ] (d : ℕ) (c : Fin d × Exponent σ → k) (i : Fin d) :
    MvPolynomial.map (algebraMap k K) (parameterTuple k σ d c i).val =
      (parameterTuple K σ d (algebraMap k K ∘ c) i).val :=
  parameterTuple_map (algebraMap k K) d c i

open Lean in
run_cmd do
  for name in #[``parameterTuple_repr, ``parameterBasis_map, ``parameterTuple_map,
      ``exists_goodOffDiagonalParameters] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Uniform original off-diagonal fiber parameters: standard foundations only."
