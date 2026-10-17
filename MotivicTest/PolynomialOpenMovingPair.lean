/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.PolynomialOpenMovingPair
public import Lean.Util.CollectAxioms
/-! Actual polynomial moving data, with no smaller-open invertibility hypothesis. -/
@[expose] public noncomputable section
open Polynomial ZeroNeighborhoodInterpolation
universe u
namespace MotivicTest.PolynomialOpenMovingPair
variable {R : Type u} [CommRing R] [Nontrivial R]
example (f g : R[X]) (hf : f.Monic) (hg : g.Monic) (hfg : IsCoprime f g)
    (a : R) (ha : IsUnit (f.eval a)) :
    ∃ d q : R[X], d.Monic ∧ q.Monic ∧
      q.natDegree = ((X - C a) * d).natDegree ∧
      IsUnit (AdjoinRoot.mk d (f * g)) ∧ IsUnit (AdjoinRoot.mk q (f * g)) ∧
      (pencil ((X - C a) * d) q).Monic ∧
      Module.Finite R[X] (AdjoinRoot (pencil ((X - C a) * d) q)) ∧
      Module.Free R[X] (AdjoinRoot (pencil ((X - C a) * d) q)) ∧
      IsUnit (AdjoinRoot.mk (pencil ((X - C a) * d) q) (f.map C)) :=
  OpenMovingPair.exists_finite_free_moving_pencil f g hf hg hfg a ha
open Lean in
run_cmd do
  for name in #[``OpenMovingPair.exists_monic_pair,
      ``OpenMovingPair.exists_finite_free_moving_pencil] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual polynomial open moving pair: standard foundations only."
end MotivicTest.PolynomialOpenMovingPair
