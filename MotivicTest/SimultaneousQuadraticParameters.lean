/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.SimultaneousQuadraticParameters
public import Lean

/-! # Actual one-tuple smooth, étale and full-infinity conditions with no open premise -/
public noncomputable section
open MvPolynomial AlgebraicGeometry QuadraticIncidence
universe u

example (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal] (I : Ideal R) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k),
      InfinityChart.NoCommonClosedInfinityZero k R I g d c ∧
      InfinityChart.NoCommonInfinityZero k R g d (prependParameters k d a c) ∧
      (∃ r ∉ P.asIdeal, ((algebraMap R (Localization.Away r)).comp
        (aeval (R := k) (fun i => aeval g
          (parameterTuple k σ (d + 1) (prependParameters k d a c) i).val)).toRingHom).Etale) ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r ∉ Q.asIdeal, SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) := by
  obtain ⟨a, c, _, hZ, hW, he, hs⟩ := exists_simultaneous_quadratic_parameters
    k R P I hI g hg d hd 1 one_ne_zero
  exact ⟨a, c, hZ, hW, he, hs⟩

open Lean in
run_cmd do
  for name in #[``exists_simultaneous_quadratic_parameters,
      ``exists_selectedEtale_open, ``exists_fullSelectedPoint_open,
      ``exists_wholeFiber_etale_infinity] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "One original tuple: whole-fiber smooth, full-map etale, W/Z infinity, standard axioms."
