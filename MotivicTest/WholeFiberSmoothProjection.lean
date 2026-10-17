/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberSmoothProjection
public import Lean

/-! # One original projection and every prime of its selected fiber -/
public noncomputable section
open Module TensorProduct KaehlerDifferential MvPolynomial AlgebraicGeometry QuadraticIncidence
universe u
namespace MotivicTest.WholeFiberSmoothProjection

/-- No good-fiber, differential, or field-lifting hypothesis is supplied. -/
theorem original_projection_whole_fiber (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (P : PrimeSpectrum R) [P.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      let f : Fin d → R := fun i => aeval g (parameterTuple k σ d c i).val
      ∀ Q : PrimeSpectrum R,
        Ideal.comap (aeval (R := k) f).toRingHom P.asIdeal =
          Ideal.comap (aeval (R := k) f).toRingHom Q.asIdeal →
        ∃ r : R, Q ∈ PrimeSpectrum.basicOpen r ∧ SmoothOfRelativeDimension 1
          (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
            (aeval (R := k) f).toRingHom))) :=
  exists_wholeFiber_smooth_projection k R P g hg d hd q hq

open Lean in
run_cmd do
  for name in #[``original_projection_whole_fiber, ``eval_map_original_function,
      ``exists_wholeFiber_smooth_projection] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original projection, every fiber prime, native relative smoothness: audited."

end MotivicTest.WholeFiberSmoothProjection
